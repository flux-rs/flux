// This code was adapted from
// [Rust Analyzer](https://github.com/rust-analyzer/rust-analyzer/blob/9d33d05d85456c855b88a8bdf4ab44d97e32bd4a/crates/hir_def/src/intern.rs)
// Rust Analyzer is distributed under the MIT License and the Apache License (Version 2.0), both reproduced below.

// ========================================================
// LICENSE-MIT
// ========================================================
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:

// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

// ==========================================================================
// LICENSE-APACHE
// ==========================================================================
//     Apache License
//                         Version 2.0, January 2004
//                      http://www.apache.org/licenses/

// TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

// 1. Definitions.

//    "License" shall mean the terms and conditions for use, reproduction,
//    and distribution as defined by Sections 1 through 9 of this document.

//    "Licensor" shall mean the copyright owner or entity authorized by
//    the copyright owner that is granting the License.

//    "Legal Entity" shall mean the union of the acting entity and all
//    other entities that control, are controlled by, or are under common
//    control with that entity. For the purposes of this definition,
//    "control" means (i) the power, direct or indirect, to cause the
//    direction or management of such entity, whether by contract or
//    otherwise, or (ii) ownership of fifty percent (50%) or more of the
//    outstanding shares, or (iii) beneficial ownership of such entity.

//    "You" (or "Your") shall mean an individual or Legal Entity
//    exercising permissions granted by this License.

//    "Source" form shall mean the preferred form for making modifications,
//    including but not limited to software source code, documentation
//    source, and configuration files.

//    "Object" form shall mean any form resulting from mechanical
//    transformation or translation of a Source form, including but
//    not limited to compiled object code, generated documentation,
//    and conversions to other media types.

//    "Work" shall mean the work of authorship, whether in Source or
//    Object form, made available under the License, as indicated by a
//    copyright notice that is included in or attached to the work
//    (an example is provided in the Appendix below).

//    "Derivative Works" shall mean any work, whether in Source or Object
//    form, that is based on (or derived from) the Work and for which the
//    editorial revisions, annotations, elaborations, or other modifications
//    represent, as a whole, an original work of authorship. For the purposes
//    of this License, Derivative Works shall not include works that remain
//    separable from, or merely link (or bind by name) to the interfaces of,
//    the Work and Derivative Works thereof.

//    "Contribution" shall mean any work of authorship, including
//    the original version of the Work and any modifications or additions
//    to that Work or Derivative Works thereof, that is intentionally
//    submitted to Licensor for inclusion in the Work by the copyright owner
//    or by an individual or Legal Entity authorized to submit on behalf of
//    the copyright owner. For the purposes of this definition, "submitted"
//    means any form of electronic, verbal, or written communication sent
//    to the Licensor or its representatives, including but not limited to
//    communication on electronic mailing lists, source code control systems,
//    and issue tracking systems that are managed by, or on behalf of, the
//    Licensor for the purpose of discussing and improving the Work, but
//    excluding communication that is conspicuously marked or otherwise
//    designated in writing by the copyright owner as "Not a Contribution."

//    "Contributor" shall mean Licensor and any individual or Legal Entity
//    on behalf of whom a Contribution has been received by Licensor and
//    subsequently incorporated within the Work.

// 2. Grant of Copyright License. Subject to the terms and conditions of
//    this License, each Contributor hereby grants to You a perpetual,
//    worldwide, non-exclusive, no-charge, royalty-free, irrevocable
//    copyright license to reproduce, prepare Derivative Works of,
//    publicly display, publicly perform, sublicense, and distribute the
//    Work and such Derivative Works in Source or Object form.

// 3. Grant of Patent License. Subject to the terms and conditions of
//    this License, each Contributor hereby grants to You a perpetual,
//    worldwide, non-exclusive, no-charge, royalty-free, irrevocable
//    (except as stated in this section) patent license to make, have made,
//    use, offer to sell, sell, import, and otherwise transfer the Work,
//    where such license applies only to those patent claims licensable
//    by such Contributor that are necessarily infringed by their
//    Contribution(s) alone or by combination of their Contribution(s)
//    with the Work to which such Contribution(s) was submitted. If You
//    institute patent litigation against any entity (including a
//    cross-claim or counterclaim in a lawsuit) alleging that the Work
//    or a Contribution incorporated within the Work constitutes direct
//    or contributory patent infringement, then any patent licenses
//    granted to You under this License for that Work shall terminate
//    as of the date such litigation is filed.

// 4. Redistribution. You may reproduce and distribute copies of the
//    Work or Derivative Works thereof in any medium, with or without
//    modifications, and in Source or Object form, provided that You
//    meet the following conditions:

//    (a) You must give any other recipients of the Work or
//        Derivative Works a copy of this License; and

//    (b) You must cause any modified files to carry prominent notices
//        stating that You changed the files; and

//    (c) You must retain, in the Source form of any Derivative Works
//        that You distribute, all copyright, patent, trademark, and
//        attribution notices from the Source form of the Work,
//        excluding those notices that do not pertain to any part of
//        the Derivative Works; and

//    (d) If the Work includes a "NOTICE" text file as part of its
//        distribution, then any Derivative Works that You distribute must
//        include a readable copy of the attribution notices contained
//        within such NOTICE file, excluding those notices that do not
//        pertain to any part of the Derivative Works, in at least one
//        of the following places: within a NOTICE text file distributed
//        as part of the Derivative Works; within the Source form or
//        documentation, if provided along with the Derivative Works; or,
//        within a display generated by the Derivative Works, if and
//        wherever such third-party notices normally appear. The contents
//        of the NOTICE file are for informational purposes only and
//        do not modify the License. You may add Your own attribution
//        notices within Derivative Works that You distribute, alongside
//        or as an addendum to the NOTICE text from the Work, provided
//        that such additional attribution notices cannot be construed
//        as modifying the License.

//    You may add Your own copyright statement to Your modifications and
//    may provide additional or different license terms and conditions
//    for use, reproduction, or distribution of Your modifications, or
//    for any such Derivative Works as a whole, provided Your use,
//    reproduction, and distribution of the Work otherwise complies with
//    the conditions stated in this License.

// 5. Submission of Contributions. Unless You explicitly state otherwise,
//    any Contribution intentionally submitted for inclusion in the Work
//    by You to the Licensor shall be under the terms and conditions of
//    this License, without any additional terms or conditions.
//    Notwithstanding the above, nothing herein shall supersede or modify
//    the terms of any separate license agreement you may have executed
//    with Licensor regarding such Contributions.

// 6. Trademarks. This License does not grant permission to use the trade
//    names, trademarks, service marks, or product names of the Licensor,
//    except as required for reasonable and customary use in describing the
//    origin of the Work and reproducing the content of the NOTICE file.

// 7. Disclaimer of Warranty. Unless required by applicable law or
//    agreed to in writing, Licensor provides the Work (and each
//    Contributor provides its Contributions) on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
//    implied, including, without limitation, any warranties or conditions
//    of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
//    PARTICULAR PURPOSE. You are solely responsible for determining the
//    appropriateness of using or redistributing the Work and assume any
//    risks associated with Your exercise of permissions under this License.

// 8. Limitation of Liability. In no event and under no legal theory,
//    whether in tort (including negligence), contract, or otherwise,
//    unless required by applicable law (such as deliberate and grossly
//    negligent acts) or agreed to in writing, shall any Contributor be
//    liable to You for damages, including any direct, indirect, special,
//    incidental, or consequential damages of any character arising as a
//    result of this License or out of the use or inability to use the
//    Work (including but not limited to damages for loss of goodwill,
//    work stoppage, computer failure or malfunction, or any and all
//    other commercial damages or losses), even if such Contributor
//    has been advised of the possibility of such damages.

// 9. Accepting Warranty or Additional Liability. While redistributing
//    the Work or Derivative Works thereof, You may choose to offer,
//    and charge a fee for, acceptance of support, warranty, indemnity,
//    or other liability obligations and/or rights consistent with this
//    License. However, in accepting such obligations, You may act only
//    on Your own behalf and on Your sole responsibility, not on behalf
//    of any other Contributor, and only if You agree to indemnify,
//    defend, and hold each Contributor harmless for any liability
//    incurred by, or claims asserted against, such Contributor by reason
//    of your accepting any such warranty or additional liability.

// END OF TERMS AND CONDITIONS

// APPENDIX: How to apply the Apache License to your work.

//    To apply the Apache License to your work, attach the following
//    boilerplate notice, with the fields enclosed by brackets "[]"
//    replaced with your own identifying information. (Don't include
//    the brackets!)  The text should be enclosed in the appropriate
//    comment syntax for the file format. We also recommend that a
//    file or class name and description of purpose be included on the
//    same "printed page" as the copyright notice for easier
//    identification within third-party archives.

// Copyright [yyyy] [name of copyright owner]

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at

// 	http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Global `Arc`-based object interning infrastructure.
//!
//! Eventually this should probably be replaced with salsa-based interning.

use std::{
    collections::HashMap,
    fmt::{self, Debug, Display},
    hash::{BuildHasherDefault, Hash, Hasher},
    ops::Deref,
    sync::{Arc, OnceLock},
};

use dashmap::{lock::RwLockWriteGuard, DashMap, SharedValue};
use rustc_hash::FxHasher;

type InternMap<T> = DashMap<Arc<T>, (), BuildHasherDefault<FxHasher>>;
type Guard<T> =
    RwLockWriteGuard<'static, HashMap<Arc<T>, SharedValue<()>, BuildHasherDefault<FxHasher>>>;

pub struct Interned<T: Internable + ?Sized> {
    arc: Arc<T>,
}

pub type List<T> = Interned<[T]>;

impl<T: Internable> Interned<T> {
    pub fn new(obj: T) -> Self {
        match Interned::lookup(&obj) {
            Ok(this) => this,
            Err(shard) => {
                let arc = Arc::new(obj);
                Self::alloc(arc, shard)
            }
        }
    }
}

impl<T> List<T>
where
    [T]: Internable,
{
    pub fn from_vec(vec: Vec<T>) -> List<T> {
        match Interned::lookup(vec.as_slice()) {
            Ok(this) => this,
            Err(shard) => {
                let arc = Arc::from(vec);
                Self::alloc(arc, shard)
            }
        }
    }
}

impl<T> From<&[T]> for Interned<[T]>
where
    [T]: Internable,
    T: Clone,
{
    fn from(slice: &[T]) -> Self {
        match Interned::lookup(slice) {
            Ok(this) => this,
            Err(shard) => {
                let arc = Arc::from(slice);
                Self::alloc(arc, shard)
            }
        }
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
    fn lookup(obj: &T) -> Result<Self, Guard<T>> {
        let storage = T::storage().get();
        let shard_idx = storage.determine_map(obj);
        let shard = &storage.shards()[shard_idx];
        let shard = shard.write();

        // Atomically,
        // - check if `obj` is already in the map
        //   - if so, clone its `Arc` and return it
        //   - if not, box it up, insert it, and return a clone
        // This needs to be atomic (locking the shard) to avoid races with other thread, which could
        // insert the same object between us looking it up and inserting it.

        // FIXME: avoid double lookup/hashing by using raw entry API (once stable, or when
        // hashbrown can be plugged into dashmap)
        match shard.get_key_value(obj) {
            Some((arc, _)) => Ok(Self { arc: arc.clone() }),
            None => Err(shard),
        }
    }

    fn alloc(arc: Arc<T>, mut shard: Guard<T>) -> Self {
        let arc2 = arc.clone();

        shard.insert(arc2, SharedValue::new(()));

        Self { arc }
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
        let storage = T::storage().get();
        let shard_idx = storage.determine_map(&self.arc);
        let shard = &storage.shards()[shard_idx];
        let mut shard = shard.write();

        // FIXME: avoid double lookup
        let (arc, _) = shard
            .get_key_value(&self.arc)
            .expect("interned value removed prematurely");

        if Arc::strong_count(arc) != 2 {
            // Another thread has interned another copy
            return;
        }

        shard.remove(&self.arc);

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
        state.write_usize(Arc::as_ptr(&self.arc) as *const () as usize)
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

/// Implements `Internable` for a given list of types, making them usable with `Interned`.
#[macro_export]
#[doc(hidden)]
macro_rules! _impl_internable {
    ( $($t:ty),+ $(,)? ) => { $(
        impl $crate::intern::Internable for $t {
            fn storage() -> &'static $crate::intern::InternStorage<Self> {
                static STORAGE: $crate::intern::InternStorage<$t> = $crate::intern::InternStorage::new();
                &STORAGE
            }
        }
    )+ };
}

pub use crate::_impl_internable as impl_internable;
