//! Untyped configuration values that remember where they were written.
//!
//! Configuration files are parsed into [`ConfigValue`] trees in which every node carries its
//! [`Location`]. Trees from different files are merged and then deserialized into typed settings.
//! Deserialization errors point to the location of the offending value, and fields of type
//! [`Located<T>`] keep the location of their value, e.g., to resolve a relative path against the
//! file that defines it.

use std::{
    collections::{BTreeMap, btree_map},
    fmt, fs,
    marker::PhantomData,
    ops::Range,
    vec,
};

use anyhow::{Context, bail};
use cargo_metadata::camino::{Utf8Path, Utf8PathBuf};
use serde::{
    Deserialize, Deserializer,
    de::{
        self, DeserializeOwned, DeserializeSeed, IgnoredAny, IntoDeserializer, MapAccess,
        SeqAccess, Visitor,
        value::{MapDeserializer, StrDeserializer},
    },
    forward_to_deserialize_any,
};
use toml::{
    Spanned,
    de::{DeTable, DeValue},
};

/// Where a configuration value was written.
#[derive(Clone, Debug)]
pub struct Location {
    /// The configuration file, `<base>/<dir>/config.toml`, where `<dir>` is `.flux` or the Flux
    /// home.
    path: Utf8PathBuf,
    /// Byte range of the value in the file.
    span: Range<usize>,
}

impl Location {
    /// Directory that relative paths resolve against: the parent of the directory containing the
    /// file.
    fn base(&self) -> &Utf8Path {
        let dir = self.path.parent().unwrap_or(&self.path);
        dir.parent().unwrap_or(dir)
    }
}

impl fmt::Display for Location {
    /// Formats the location as `path:line:column`. The file is read again to find the line and
    /// column, which only happens when reporting errors.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let line_column = fs::read_to_string(&self.path)
            .ok()
            .and_then(|contents| line_column(&contents, self.span.start));
        match line_column {
            Some((line, column)) => write!(f, "{}:{line}:{column}", self.path),
            None => write!(f, "{}", self.path),
        }
    }
}

/// One-based line and column of the byte `offset` in `contents`.
fn line_column(contents: &str, offset: usize) -> Option<(usize, usize)> {
    let before = contents.get(..offset)?;
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    Some((before.matches('\n').count() + 1, before[line_start..].chars().count() + 1))
}

/// A configuration value together with its [`Location`]. It can only be deserialized from a
/// [`ConfigValue`].
#[derive(Clone, Debug)]
pub struct Located<T> {
    pub value: T,
    pub location: Location,
}

impl Located<Utf8PathBuf> {
    /// Resolves the path against the directory of the file that defines it.
    pub fn resolve(&self) -> Utf8PathBuf {
        self.location.base().join(&self.value)
    }
}

/// Name and fields of the struct through which a [`ConfigValue`] hands a value and its location to
/// [`Located`]. They cannot clash with the name of any other struct.
const LOCATED: &str = "$__flux_private_Located";
const VALUE_FIELD: &str = "$__flux_private_value";
const LOCATION_FIELD: &str = "$__flux_private_location";

impl<'de, T: Deserialize<'de>> Deserialize<'de> for Located<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct LocatedVisitor<T>(PhantomData<T>);

        impl<'de, T: Deserialize<'de>> Visitor<'de> for LocatedVisitor<T> {
            type Value = Located<T>;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str("a value from a configuration file")
            }

            fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Located<T>, A::Error> {
                let (_, value) = map
                    .next_entry::<IgnoredAny, T>()?
                    .ok_or_else(|| de::Error::missing_field(VALUE_FIELD))?;
                let (_, (path, start, end)) = map
                    .next_entry::<IgnoredAny, (Utf8PathBuf, usize, usize)>()?
                    .ok_or_else(|| de::Error::missing_field(LOCATION_FIELD))?;
                Ok(Located { value, location: Location { path, span: start..end } })
            }
        }

        deserializer.deserialize_struct(
            LOCATED,
            &[VALUE_FIELD, LOCATION_FIELD],
            LocatedVisitor(PhantomData),
        )
    }
}

/// An untyped configuration value. Every node remembers its [`Location`].
#[derive(Clone, Debug)]
pub enum ConfigValue {
    String(String, Location),
    Integer(i64, Location),
    Boolean(bool, Location),
    List(Vec<ConfigValue>, Location),
    Table(BTreeMap<String, ConfigValue>, Location),
}

impl ConfigValue {
    /// Parses a configuration file.
    pub fn parse_file(path: &Utf8Path) -> anyhow::Result<ConfigValue> {
        let contents =
            fs::read_to_string(path).with_context(|| format!("failed to read `{path}`"))?;
        let table =
            DeTable::parse(&contents).with_context(|| format!("failed to parse `{path}`"))?;
        let location = Location { path: path.to_owned(), span: table.span() };
        Self::from_table(table.into_inner(), location)
    }

    fn from_spanned(value: Spanned<DeValue>, path: &Utf8Path) -> anyhow::Result<ConfigValue> {
        let location = Location { path: path.to_owned(), span: value.span() };
        Ok(match value.into_inner() {
            DeValue::String(s) => ConfigValue::String(s.into_owned(), location),
            DeValue::Integer(i) => {
                let Ok(i) = i64::from_str_radix(i.as_str(), i.radix()) else {
                    bail!("{location}: integer out of range");
                };
                ConfigValue::Integer(i, location)
            }
            DeValue::Boolean(b) => ConfigValue::Boolean(b, location),
            DeValue::Array(array) => {
                let items = array
                    .into_iter()
                    .map(|item| Self::from_spanned(item, path))
                    .collect::<anyhow::Result<_>>()?;
                ConfigValue::List(items, location)
            }
            DeValue::Table(table) => Self::from_table(table, location)?,
            DeValue::Float(_) => bail!("{location}: floats are not supported"),
            DeValue::Datetime(_) => bail!("{location}: dates and times are not supported"),
        })
    }

    fn from_table(table: DeTable, location: Location) -> anyhow::Result<ConfigValue> {
        let entries = table
            .into_iter()
            .map(|(key, value)| {
                Ok((key.into_inner().into_owned(), Self::from_spanned(value, &location.path)?))
            })
            .collect::<anyhow::Result<_>>()?;
        Ok(ConfigValue::Table(entries, location))
    }

    pub fn location(&self) -> &Location {
        match self {
            ConfigValue::String(_, location)
            | ConfigValue::Integer(_, location)
            | ConfigValue::Boolean(_, location)
            | ConfigValue::List(_, location)
            | ConfigValue::Table(_, location) => location,
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            ConfigValue::Table(..) => "a table",
            ConfigValue::List(..) => "an array",
            _ => "a value",
        }
    }

    /// Removes `key` if `self` is a table.
    pub fn remove(&mut self, key: &str) -> Option<ConfigValue> {
        match self {
            ConfigValue::Table(entries, _) => entries.remove(key),
            _ => None,
        }
    }

    /// Merges values ordered from lowest to highest precedence. Returns `None` if there are none.
    pub fn merge_all(
        values: impl IntoIterator<Item = ConfigValue>,
    ) -> anyhow::Result<Option<ConfigValue>> {
        let mut merged: Option<ConfigValue> = None;
        for value in values {
            match &mut merged {
                Some(merged) => merged.merge(value, "")?,
                None => merged = Some(value),
            }
        }
        Ok(merged)
    }

    /// Merges `src` into `self`, where `src` has higher precedence. Tables are merged key by key,
    /// arrays are concatenated, and any other value is replaced.
    fn merge(&mut self, src: ConfigValue, key: &str) -> anyhow::Result<()> {
        match (self, src) {
            (ConfigValue::Table(dst, _), ConfigValue::Table(src, _)) => {
                for (src_key, src_value) in src {
                    let full_key =
                        if key.is_empty() { src_key.clone() } else { format!("{key}.{src_key}") };
                    match dst.get_mut(&src_key) {
                        Some(dst_value) => dst_value.merge(src_value, &full_key)?,
                        None => {
                            dst.insert(src_key, src_value);
                        }
                    }
                }
            }
            (ConfigValue::List(dst, _), ConfigValue::List(src, _)) => dst.extend(src),
            (dst, src) if dst.kind() == src.kind() => *dst = src,
            (dst, src) => {
                bail!(
                    "`{key}` is {} in {} but {} in {}",
                    dst.kind(),
                    dst.location(),
                    src.kind(),
                    src.location()
                );
            }
        }
        Ok(())
    }

    /// Deserializes the value into `T`.
    pub fn deserialize_into<T: DeserializeOwned>(self) -> Result<T, ConfigError> {
        let location = self.location().clone();
        T::deserialize(self).map_err(|err| err.at_location(&location))
    }
}

/// An error deserializing a [`ConfigValue`].
#[derive(Debug)]
pub struct ConfigError {
    message: String,
    /// Keys leading to the value that caused the error, outermost first.
    keys: Vec<String>,
    /// Location of the value that caused the error.
    location: Option<Location>,
}

impl ConfigError {
    /// Records that the error happened inside the value of `key`.
    fn in_key(mut self, key: &str) -> Self {
        self.keys.insert(0, key.to_owned());
        self
    }

    /// Records the location of the error unless a more precise one is already known.
    fn at_location(mut self, location: &Location) -> Self {
        self.location.get_or_insert_with(|| location.clone());
        self
    }
}

impl de::Error for ConfigError {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        ConfigError { message: msg.to_string(), keys: vec![], location: None }
    }
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(location) = &self.location {
            write!(f, "{location}: ")?;
        }
        if !self.keys.is_empty() {
            write!(f, "`{}`: ", self.keys.join("."))?;
        }
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ConfigError {}

impl<'de> Deserializer<'de> for ConfigValue {
    type Error = ConfigError;

    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ConfigError> {
        match self {
            ConfigValue::String(s, _) => visitor.visit_string(s),
            ConfigValue::Integer(i, _) => visitor.visit_i64(i),
            ConfigValue::Boolean(b, _) => visitor.visit_bool(b),
            ConfigValue::List(items, _) => {
                visitor.visit_seq(ListAccess { items: items.into_iter() })
            }
            ConfigValue::Table(entries, _) => {
                visitor.visit_map(TableAccess { entries: entries.into_iter(), value: None })
            }
        }
    }

    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value, ConfigError> {
        // Missing keys never get here, they are handled by `#[serde(default)]`
        visitor.visit_some(self)
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, ConfigError> {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, ConfigError> {
        match self {
            ConfigValue::String(s, _) => visitor.visit_enum(s.into_deserializer()),
            value => value.deserialize_any(visitor),
        }
    }

    fn deserialize_struct<V: Visitor<'de>>(
        self,
        name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, ConfigError> {
        if name == LOCATED {
            // Hand the location to `Located` as a `(path, start, end)` tuple
            let location = self.location().clone();
            let encoded = ConfigValue::List(
                vec![
                    ConfigValue::String(location.path.to_string(), location.clone()),
                    ConfigValue::Integer(location.span.start as i64, location.clone()),
                    ConfigValue::Integer(location.span.end as i64, location.clone()),
                ],
                location,
            );
            let fields = [(VALUE_FIELD, self), (LOCATION_FIELD, encoded)];
            return visitor.visit_map(MapDeserializer::new(fields.into_iter()));
        }
        self.deserialize_any(visitor)
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string bytes byte_buf unit
        unit_struct seq tuple tuple_struct map identifier ignored_any
    }
}

impl<'de> IntoDeserializer<'de, ConfigError> for ConfigValue {
    type Deserializer = Self;

    fn into_deserializer(self) -> Self {
        self
    }
}

struct TableAccess {
    entries: btree_map::IntoIter<String, ConfigValue>,
    /// The entry whose key was deserialized last.
    value: Option<(String, ConfigValue)>,
}

impl<'de> MapAccess<'de> for TableAccess {
    type Error = ConfigError;

    fn next_key_seed<K: DeserializeSeed<'de>>(
        &mut self,
        seed: K,
    ) -> Result<Option<K::Value>, ConfigError> {
        let Some((key, value)) = self.entries.next() else { return Ok(None) };
        let deserializer: StrDeserializer<ConfigError> = key.as_str().into_deserializer();
        // An unknown key is reported at the location of its value
        let result = seed
            .deserialize(deserializer)
            .map_err(|err| err.at_location(value.location()));
        self.value = Some((key, value));
        result.map(Some)
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(
        &mut self,
        seed: V,
    ) -> Result<V::Value, ConfigError> {
        let (key, value) = self
            .value
            .take()
            .expect("`next_value_seed` called before `next_key_seed`");
        let location = value.location().clone();
        seed.deserialize(value)
            .map_err(|err| err.at_location(&location).in_key(&key))
    }
}

struct ListAccess {
    items: vec::IntoIter<ConfigValue>,
}

impl<'de> SeqAccess<'de> for ListAccess {
    type Error = ConfigError;

    fn next_element_seed<T: DeserializeSeed<'de>>(
        &mut self,
        seed: T,
    ) -> Result<Option<T::Value>, ConfigError> {
        let Some(item) = self.items.next() else { return Ok(None) };
        let location = item.location().clone();
        seed.deserialize(item)
            .map(Some)
            .map_err(|err| err.at_location(&location))
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.items.len())
    }
}
