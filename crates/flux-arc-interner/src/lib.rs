//! Global `Arc`-based object interning infrastructure.
//!
//! This code was adapted from [Rust Analyzer](https://github.com/rust-analyzer/rust-analyzer/blob/9d33d05d85456c855b88a8bdf4ab44d97e32bd4a/crates/hir_def/src/intern.rs)

#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_serialize;
// extern crate rustc_target;

use std::{
    fmt::{self, Debug, Display},
    hash::{BuildHasherDefault, Hash, Hasher},
    ops::Deref,
    sync::{Arc, OnceLock},
};

use dashmap::{DashMap, SharedValue};
use hashbrown::{HashMap, hash_map::RawEntryMut};
use rustc_hash::FxHasher;
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};

type InternMap<T> = DashMap<Arc<T>, (), BuildHasherDefault<FxHasher>>;
type Guard<T> = dashmap::RwLockWriteGuard<
    'static,
    HashMap<Arc<T>, SharedValue<()>, BuildHasherDefault<FxHasher>>,
>;

pub struct Interned<T: Internable + ?Sized> {
    arc: Arc<T>,
}

pub type List<T> = Interned<[T]>;

impl<T> Default for List<T>
where
    [T]: Internable,
{
    fn default() -> Self {
        Self::from_arr([])
    }
}

impl<T: Internable> Interned<T> {
    pub fn new(obj: T) -> Self {
        let (mut shard, hash) = Self::select(&obj);
        match shard.raw_entry_mut().from_key_hashed_nocheck(hash, &obj) {
            RawEntryMut::Occupied(occ) => Self { arc: occ.key().clone() },
            RawEntryMut::Vacant(vac) => {
                Self {
                    arc: vac
                        .insert_hashed_nocheck(hash, Arc::new(obj), SharedValue::new(()))
                        .0
                        .clone(),
                }
            }
        }
    }
}

impl<T> List<T>
where
    [T]: Internable,
{
    fn list_with<S>(obj: S, to_arc: impl FnOnce(S) -> Arc<[T]>) -> List<T>
    where
        S: std::borrow::Borrow<[T]>,
    {
        let (mut shard, hash) = Self::select(obj.borrow());
        match shard
            .raw_entry_mut()
            .from_key_hashed_nocheck(hash, obj.borrow())
        {
            RawEntryMut::Occupied(occ) => Self { arc: occ.key().clone() },
            RawEntryMut::Vacant(vac) => {
                Self {
                    arc: vac
                        .insert_hashed_nocheck(hash, to_arc(obj), SharedValue::new(()))
                        .0
                        .clone(),
                }
            }
        }
    }

    pub fn from_vec(vec: Vec<T>) -> List<T> {
        List::list_with(vec, Arc::from)
    }

    pub fn from_arr<const N: usize>(arr: [T; N]) -> List<T> {
        List::list_with(arr, |arr| Arc::new(arr))
    }

    pub fn empty() -> List<T> {
        Self::from_arr([])
    }

    pub fn singleton(x: T) -> List<T> {
        Self::from_arr([x])
    }
}

impl<T> List<T>
where
    T: Clone,
    [T]: Internable,
{
    pub fn from_slice(slice: &[T]) -> List<T> {
        List::list_with(slice, Arc::from)
    }
}

impl<T> FromIterator<T> for List<T>
where
    [T]: Internable,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_vec(iter.into_iter().collect())
    }
}

impl<T> From<&[T]> for Interned<[T]>
where
    [T]: Internable,
    T: Clone,
{
    fn from(slice: &[T]) -> Self {
        List::from_slice(slice)
    }
}

impl<T> From<Vec<T>> for Interned<[T]>
where
    [T]: Internable,
{
    fn from(vec: Vec<T>) -> Self {
        List::from_vec(vec)
    }
}

impl<T: Internable + ?Sized> Interned<T> {
    #[inline]
    fn select(obj: &T) -> (Guard<T>, u64) {
        let storage = T::storage().get();
        let hash = {
            let mut hasher = std::hash::BuildHasher::build_hasher(storage.hasher());
            obj.hash(&mut hasher);
            hasher.finish()
        };
        let shard_idx = storage.determine_shard(hash as usize);
        let shard = &storage.shards()[shard_idx];
        (shard.write(), hash)
    }
}

impl<T: Internable + ?Sized> Drop for Interned<T> {
    #[inline]
    fn drop(&mut self) {
        // When the last `Ref` is dropped, remove the object from the global map.
        if Arc::strong_count(&self.arc) == 2 {
            // Only `self` and the global map point to the object.
            self.drop_slow();
        }
    }
}

impl<T: Internable + ?Sized> Interned<T> {
    #[cold]
    fn drop_slow(&mut self) {
        let (mut shard, hash) = Self::select(&self.arc);

        if Arc::strong_count(&self.arc) != 2 {
            // Another thread has interned another copy
            return;
        }

        match shard
            .raw_entry_mut()
            .from_key_hashed_nocheck(hash, &self.arc)
        {
            RawEntryMut::Occupied(occ) => occ.remove(),
            RawEntryMut::Vacant(_) => unreachable!(),
        };

        // Shrink the backing storage if the shard is less than 50% occupied.
        if shard.len() * 2 < shard.capacity() {
            shard.shrink_to_fit();
        }
    }
}

/// Compares interned `Ref`s using pointer equality.
impl<T: Internable> PartialEq for Interned<T> {
    // NOTE: No `?Sized` because `ptr_eq` doesn't work right with trait objects.

    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.arc, &other.arc)
    }
}

impl<T: Internable> Eq for Interned<T> {}

impl<T> PartialEq for Interned<[T]>
where
    [T]: Internable,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.arc, &other.arc)
    }
}

impl<T> Eq for Interned<[T]> where [T]: Internable {}

impl<T: Internable + ?Sized> Hash for Interned<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // NOTE: Cast disposes vtable pointer / slice/str length.
        state.write_usize(Arc::as_ptr(&self.arc) as *const () as usize);
    }
}

impl<T: PartialOrd + Internable> PartialOrd for Interned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        <T as PartialOrd>::partial_cmp(&self.arc, &other.arc)
    }
}

impl<T: Ord + Internable> Ord for Interned<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        <T as Ord>::cmp(&self.arc, &other.arc)
    }
}

impl<T> PartialOrd for List<T>
where
    T: PartialOrd,
    [T]: Internable,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        <[T] as PartialOrd>::partial_cmp(&self.arc, &other.arc)
    }
}

impl<T> Ord for List<T>
where
    T: Ord,
    [T]: Internable,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        <[T] as Ord>::cmp(&self.arc, &other.arc)
    }
}

impl<T: Internable + ?Sized> AsRef<T> for Interned<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.arc
    }
}

impl<T: Internable + ?Sized> Deref for Interned<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.arc
    }
}

impl<T: Internable + ?Sized> Clone for Interned<T> {
    fn clone(&self) -> Self {
        Self { arc: self.arc.clone() }
    }
}

impl<T: Debug + Internable + ?Sized> Debug for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.arc).fmt(f)
    }
}

impl<T: Display + Internable + ?Sized> Display for Interned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.arc).fmt(f)
    }
}

impl<'a, T> IntoIterator for &'a Interned<[T]>
where
    [T]: Internable,
{
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<E, T> Encodable<E> for Interned<T>
where
    E: Encoder,
    T: Encodable<E> + Internable,
{
    fn encode(&self, s: &mut E) {
        (**self).encode(s);
    }
}

impl<D, T> Decodable<D> for Interned<T>
where
    D: Decoder,
    T: Decodable<D> + Internable,
{
    fn decode(d: &mut D) -> Self {
        Interned::new(T::decode(d))
    }
}

impl<E, T> Encodable<E> for Interned<[T]>
where
    E: Encoder,
    T: Encodable<E>,
    [T]: Internable,
{
    fn encode(&self, s: &mut E) {
        (**self).encode(s);
    }
}

impl<D, T> Decodable<D> for Interned<[T]>
where
    D: Decoder,
    T: Decodable<D>,
    [T]: Internable,
{
    fn decode(d: &mut D) -> Self {
        Interned::from_vec(Decodable::decode(d))
    }
}

pub struct InternStorage<T: ?Sized> {
    map: OnceLock<InternMap<T>>,
}

impl<T: ?Sized> InternStorage<T> {
    pub const fn new() -> Self {
        Self { map: OnceLock::new() }
    }
}

impl<T: Internable + ?Sized> InternStorage<T> {
    fn get(&self) -> &InternMap<T> {
        self.map.get_or_init(DashMap::default)
    }
}

pub trait Internable: Hash + Eq + 'static {
    fn storage() -> &'static InternStorage<Self>;
}

pub trait SliceInternable: Hash + Eq + 'static + Sized {
    fn storage() -> &'static InternStorage<[Self]>;
}

impl<T> Internable for [T]
where
    T: SliceInternable,
{
    fn storage() -> &'static InternStorage<Self> {
        <T as SliceInternable>::storage()
    }
}

/// Implements `Internable` for a given list of types, making them usable with `Interned`.
#[macro_export]
#[doc(hidden)]
macro_rules! _impl_internable {
    ( $($t:ty),+ $(,)? ) => { $(
        impl $crate::Internable for $t {
            fn storage() -> &'static $crate::InternStorage<Self> {
                static STORAGE: $crate::InternStorage<$t> = $crate::InternStorage::new();
                &STORAGE
            }
        }
    )+ };
}
pub use crate::_impl_internable as impl_internable;

/// Implements `SliceInternable` for a given list of types, making them usable as `Interned<[T]>`.
#[macro_export]
#[doc(hidden)]
macro_rules! _impl_slice_internable {
    ( $($t:ty),+ $(,)? ) => { $(
        impl $crate::SliceInternable for $t {
            fn storage() -> &'static $crate::InternStorage<[Self]> {
                static STORAGE: $crate::InternStorage<[$t]> = $crate::InternStorage::new();
                &STORAGE
            }
        }
    )+ };
}
pub use crate::_impl_slice_internable as impl_slice_internable;

impl_slice_internable!(rustc_abi::FieldIdx);
