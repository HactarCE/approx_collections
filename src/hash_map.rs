//! Hash map that works for [`ApproxHash`]able values.

use std::collections::{HashMap, hash_map};
use std::fmt;
use std::hash::{BuildHasher, BuildHasherDefault, Hasher, RandomState};
use std::iter::FusedIterator;

use smallvec::{SmallVec, smallvec};

use crate::{ApproxHash, FloatPool, Precision};

type IterInner<'a, K, V> = std::iter::Flatten<hash_map::Values<'a, u64, LinearApproxMap<K, V>>>;
type IterMutInner<'a, K, V> =
    std::iter::Flatten<hash_map::ValuesMut<'a, u64, LinearApproxMap<K, V>>>;
type IntoIterInner<K, V> = std::iter::Flatten<hash_map::IntoValues<u64, LinearApproxMap<K, V>>>;

#[derive(Debug, Default, Copy, Clone)]
struct TrivialHasher(u64);

impl Hasher for TrivialHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _bytes: &[u8]) {
        unreachable!("TrivialHasher can only be used with write_u64()");
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}

/// Approximate hash map for objects with floating-point values, using a
/// `BTreeMap` to record arbitrary hash values for floats.
#[derive(Clone)]
pub struct ApproxHashMap<K, V, S = RandomState> {
    hash_builder: S,
    pool: FloatPool,
    map: HashMap<u64, LinearApproxMap<K, V>, BuildHasherDefault<TrivialHasher>>,
    len: usize,
}

impl<K, V, S> fmt::Debug for ApproxHashMap<K, V, S>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> ApproxHashMap<K, V, RandomState> {
    /// Constructs an empty map.
    pub fn new(prec: Precision) -> ApproxHashMap<K, V, RandomState> {
        Self::with_hasher(RandomState::default(), prec)
    }
}

impl<K, V, S> ApproxHashMap<K, V, S> {
    /// Constructs an empty map which will use the given hash builder to hash
    /// keys.
    pub fn with_hasher(hash_builder: S, prec: Precision) -> ApproxHashMap<K, V, S> {
        ApproxHashMap {
            hash_builder,
            pool: FloatPool::new(prec),
            map: HashMap::default(),
            len: 0,
        }
    }

    /// Returns an iterator of all the entries in the map.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            len: self.len,
            inner: self.map.values().flatten().map(|(k, v)| (k, v)),
        }
    }
    /// Returns an iterator of mutable references to all the entries in the map.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            len: self.len,
            inner: self.map.values_mut().flatten().map(|(k, v)| (k, v)),
        }
    }

    /// Returns an iterator of all the keys in the map.
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        Keys {
            len: self.len,
            inner: self.map.values().flatten().map(|(_k, v)| v),
        }
    }
    /// Converts the map into an iterator of all its keys.
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            len: self.len,
            inner: self.map.into_values().flatten().map(|(k, _v)| k),
        }
    }

    /// Returns an iterator of all the values in the map.
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            len: self.len,
            inner: self.map.values().flatten().map(|(_k, v)| v),
        }
    }
    /// Returns an iterator of mutable references to all the values in the map.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            len: self.len,
            inner: self.map.values_mut().flatten().map(|(_k, v)| v),
        }
    }
    /// Converts the map into an iterator of all its values.
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            len: self.len,
            inner: self.map.into_values().flatten().map(|(_k, v)| v),
        }
    }

    /// Returns the number of entries in the map.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns whether the map is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// and keeps the interned floats.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns a reference to the map's [`BuildHasher`].
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns a reference to the map's [`FloatPool`].
    pub fn float_pool(&self) -> &FloatPool {
        &self.pool
    }

    /// Returns the precision used to hash floats.
    pub fn prec(&self) -> Precision {
        self.pool.prec()
    }
}

impl<K, V> ApproxHashMap<K, V, RandomState>
where
    K: ApproxHash,
{
    /// Constructs a `HashMap<K, V>` from an iterator of key-value pairs.
    ///
    /// If the iterator produces any pairs with approximately equal keys, all
    /// but one of the corresponding values will be dropped.
    pub fn from_iter<T: IntoIterator<Item = (K, V)>>(
        prec: Precision,
        iter: T,
    ) -> ApproxHashMap<K, V> {
        let mut map = ApproxHashMap::with_hasher(Default::default(), prec);
        map.extend(iter);
        map
    }

    /// Replaces all floats in `key` with interned ones that are approximately
    /// equal, returning a mutated copy of `key`.
    ///
    /// If any floats in `key` are have not already been interned, they are
    /// added to the pool and unmodified.
    #[must_use = "intern() returns a mutated copy"]
    pub fn intern(&mut self, key: K) -> K {
        self.pool.intern(key)
    }

    /// Replaces all floats in `key` with interned ones that are approximately
    /// equal.
    ///
    /// If any floats in `key` are have not already been interned, they are
    /// added to the pool and unmodified.
    pub fn intern_in_place(&mut self, key: &mut K) {
        self.pool.intern_in_place(key);
    }

    /// Replaces all floats in `key` with interned ones that are approximately
    /// equal, returning a mutated copy of `key`. Returns `None` if any floats
    /// in `key` are not already in the pool.
    #[must_use = "try_intern() returns a mutated copy"]
    pub fn try_intern(&self, key: K) -> Option<K> {
        self.pool.try_intern(key)
    }
}

impl<K, V, S> ApproxHashMap<K, V, S>
where
    K: ApproxHash,
    S: BuildHasher,
{
    /// Returns an entry in the map for in-place manipulation.
    pub fn entry(&mut self, mut key: K) -> Entry<'_, K, V> {
        let hash = self.intern_and_hash(&mut key);
        self.entry_with_interned_key(key, hash)
    }
    /// Returns an entry in the map for in-place manipulation.
    ///
    /// `key` is interned in-place.
    pub fn entry_with_mut_key(&mut self, key: &mut K) -> Entry<'_, K, V>
    where
        K: Clone,
    {
        let hash = self.intern_and_hash(key);
        self.entry_with_interned_key(key.clone(), hash)
    }
    fn entry_with_interned_key(&mut self, key: K, hash: u64) -> Entry<'_, K, V> {
        match self.map.entry(hash) {
            hash_map::Entry::Occupied(e) => match e.get().index_of(&key) {
                Some(index) => Entry::Occupied(OccupiedEntry {
                    hash_map_entry: e,
                    index,
                    len: &mut self.len,
                }),
                None => Entry::Vacant(VacantEntry {
                    hash_map_entry: hash_map::Entry::Occupied(e),
                    key,
                    len: &mut self.len,
                }),
            },
            hash_map_entry @ hash_map::Entry::Vacant(_) => Entry::Vacant(VacantEntry {
                hash_map_entry,
                key,
                len: &mut self.len,
            }),
        }
    }
    /// Returns the value in the map associated to the given key (or something
    /// approximately equal).
    pub fn get(&self, key: K) -> Option<&V> {
        Some(self.get_key_value(key)?.1)
    }
    /// Returns the existing key-value pair that corresponds to the given key,
    /// or `None` if it is not present.
    pub fn get_key_value(&self, key: K) -> Option<(&K, &V)> {
        // Early exit optimization; don't bother hashing
        if self.is_empty() {
            return None;
        }

        let (key, hash) = self.try_intern_and_hash(key)?;
        let linear_map = self.map.get(&hash)?;
        let index = linear_map.index_of(&key)?;
        let (k, v) = linear_map.key_value(index);
        Some((k, v))
    }
    /// Returns whether the map contains a key.
    pub fn contains_key(&self, key: K) -> bool {
        self.get(key).is_some()
    }
    /// Returns a mutable reference to the value corresponding to a key.
    pub fn get_mut(&mut self, mut key: K) -> Option<&mut V> {
        let hash = self.intern_and_hash(&mut key);
        let linear_map = self.map.get_mut(&hash)?;
        let index = linear_map.index_of(&key)?;
        Some(linear_map.value_mut(index))
    }
    /// Returns a mutable reference to the value corresponding to a key.
    ///
    /// `key` is interned in-place.
    pub fn get_mut_with_mut_key(&mut self, key: &mut K) -> Option<&mut V> {
        let hash = self.intern_and_hash(key);
        let linear_map = self.map.get_mut(&hash)?;
        let index = linear_map.index_of(key)?;
        Some(linear_map.value_mut(index))
    }
    /// Inserts an entry into the map and returns the old value, if any.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.entry(key) {
            Entry::Occupied(mut e) => Some(e.insert(value)),
            Entry::Vacant(e) => {
                e.insert(value);
                None
            }
        }
    }
    /// Inserts an entry into the map and returns the old value, if any.
    ///
    /// `key` is interned in-place.
    pub fn insert_with_mut_key(&mut self, key: &mut K, value: V) -> Option<V>
    where
        K: Clone,
    {
        match self.entry_with_mut_key(key) {
            Entry::Occupied(mut e) => Some(e.insert(value)),
            Entry::Vacant(e) => {
                e.insert(value);
                None
            }
        }
    }
    /// Removes an entry from the map and returns the value, or `None` if the
    /// key was not present.
    pub fn remove(&mut self, key: K) -> Option<V> {
        Some(self.remove_entry(key)?.1)
    }
    /// Removes an entry from the map and returns the key-value pair, or `None`
    /// if the key was not present.
    pub fn remove_entry(&mut self, mut key: K) -> Option<(K, V)> {
        let hash = self.intern_and_hash(&mut key);
        let linear_map = self.map.get_mut(&hash)?;
        let index = linear_map.index_of(&key)?;
        Some(linear_map.remove(index))
    }

    fn try_intern_and_hash(&self, key: K) -> Option<(K, u64)> {
        let key = self.pool.try_intern(key)?;
        let mut h = self.hash_builder.build_hasher();
        key.interned_hash(&mut h);
        let hash = h.finish();
        Some((key, hash))
    }
    fn intern_and_hash(&mut self, key: &mut K) -> u64 {
        self.pool.intern_in_place(key);
        let mut h = self.hash_builder.build_hasher();
        key.interned_hash(&mut h);
        h.finish()
    }
}
impl<K, V, S> IntoIterator for ApproxHashMap<K, V, S> {
    type Item = (K, V);

    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            len: self.len,
            #[allow(clippy::map_identity)] // needed for full generality of the macro
            inner: self.map.into_values().flatten().map(|kv| kv),
        }
    }
}
impl<'a, K, V, S> IntoIterator for &'a ApproxHashMap<K, V, S> {
    type Item = (&'a K, &'a V);

    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, K, V, S> IntoIterator for &'a mut ApproxHashMap<K, V, S> {
    type Item = (&'a K, &'a mut V);

    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

macro_rules! iterator_structs {
    (
        $(
            $(#[$attr:meta])*
            $visibility:vis struct $struct_name:ident<
                $($lt:lifetime,)?
                $K:ident,
                $V:ident
            >($inner_type:ty) -> $output_type:ty;
        )*
    ) => {
        $(
            $(#[$attr])*
            #[derive(Debug)]
            $visibility struct $struct_name<$($lt,)? $K, $V> {
                len: usize,
                inner: std::iter::Map<
                    $inner_type,
                    fn(<$inner_type as Iterator>::Item) -> $output_type,
                >,
            }
            impl<$($lt,)? $K, $V> Default for $struct_name<$($lt,)? $K, $V> {
                fn default() -> Self {
                    Self {
                        inner: <$inner_type>::default().map(|_| unreachable!()),
                        len: 0,
                    }
                }
            }
            impl<$($lt,)? $K, $V> ExactSizeIterator for $struct_name<$($lt,)? $K, $V> {
                fn len(&self) -> usize {
                    self.len
                }
            }
            impl<$($lt,)? $K, $V> FusedIterator for $struct_name<$($lt,)? $K, $V> {}
            impl<$($lt,)? $K, $V> Iterator for $struct_name<$($lt,)? $K, $V> {
                type Item = $output_type;

                fn next(&mut self) -> Option<Self::Item> {
                    self.len = self.len.saturating_sub(1);
                    self.inner.next()
                }
            }
        )*
    };
}

macro_rules! impl_clone_for_iterator_structs {
    ($($type:ident),* $(,)?) => {
        $(
            impl<'a, K, V> Clone for $type<'a, K, V> {
                fn clone(&self) -> Self {
                    Self {
                        len: self.len,
                        inner: self.inner.clone(),
                    }
                }
            }
        )*
    };
}

iterator_structs! {
    /// An owning iterator over the entries of an `ApproxHashMap`.
    pub struct IntoIter<K, V>(IntoIterInner<K, V>) -> (K, V);

    /// An owning iterator over the keys of an `ApproxHashMap`.
    pub struct IntoKeys<K, V>(IntoIterInner<K, V>) -> K;

    /// An owning iterator over the values of an `ApproxHashMap`.
    pub struct IntoValues<K, V>(IntoIterInner<K, V>) -> V;

    /// An iterator over the entries of an `ApproxHashMap`.
    pub struct Iter<'a, K, V>(IterInner<'a, K, V>) -> (&'a K, &'a V);

    /// A mutable iterator over the entries of an `ApproxHashMap`.
    pub struct IterMut<'a, K, V>(IterMutInner<'a ,K, V>) -> (&'a K, &'a mut V);

    /// An iterator over the keys of an `ApproxHashMap`.
    pub struct Keys<'a, K, V>(IterInner<'a, K, V>) -> &'a V;

    /// An iterator over the values of an `ApproxHashMap`.
    pub struct Values<'a, K, V>(IterInner<'a, K, V>) -> &'a V;

    /// A mutable iterator over the values of an `ApproxHashMap`.
    pub struct ValuesMut<'a, K, V>(IterMutInner<'a, K, V>) -> &'a mut V;
}
impl_clone_for_iterator_structs!(Iter, Keys, Values);

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`ApproxHashMap`].
///
/// [`entry`]: ApproxHashMap::entry
pub enum Entry<'a, K, V> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of
    /// the default function. This method allows for generating key-derived
    /// values for insertion by providing the default function a reference to
    /// the key that was moved during the `.entry(key)` method call.
    ///
    /// The reference to the moved key is provided so that cloning or copying
    /// the key is unnecessary, unlike with `.or_insert_with(|| ... )`.
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => {
                let value = default(&e.key);
                e.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(e) => e.key(),
            Entry::Vacant(e) => &e.key,
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Entry::Occupied(mut e) => {
                f(e.get_mut());
                Entry::Occupied(e)
            }
            Entry::Vacant(e) => Entry::Vacant(e),
        }
    }

    /// Sets the value of the entry, and returns an `OccupiedEntry`.
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Occupied(mut e) => {
                e.insert(value);
                e
            }
            Entry::Vacant(e) => e.insert_entry(value),
        }
    }
}

impl<'a, K, V: Default> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(e) => e.into_mut(),
            Entry::Vacant(e) => e.insert(Default::default()),
        }
    }
}

/// A view into an occupied entry in an `ApproxHashMap`. It is part of the
/// [`Entry`] enum.
pub struct OccupiedEntry<'a, K, V> {
    hash_map_entry: hash_map::OccupiedEntry<'a, u64, LinearApproxMap<K, V>>,
    index: usize,
    len: &'a mut usize,
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key in the entry.
    pub fn key(&self) -> &K {
        self.hash_map_entry.get().key(self.index)
    }

    /// Take the ownership of the key and value from the map.
    pub fn remove_entry(mut self) -> (K, V) {
        *self.len -= 1;
        if self.hash_map_entry.get().len() == 1 {
            self.hash_map_entry.remove_entry().1.unwrap_exactly_one()
        } else {
            self.hash_map_entry.get_mut().remove(self.index)
        }
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        self.hash_map_entry.get().value(self.index)
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: Self::into_mut
    pub fn get_mut(&mut self) -> &mut V {
        self.hash_map_entry.get_mut().value_mut(self.index)
    }

    /// Converts the `OccupiedEntry` into a mutable reference to the value in
    /// the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: Self::get_mut
    pub fn into_mut(self) -> &'a mut V {
        self.hash_map_entry.into_mut().value_mut(self.index)
    }

    /// Sets the value of the entry, and returns the entry's old value.
    pub fn insert(&mut self, value: V) -> V {
        std::mem::replace(self.get_mut(), value)
    }

    /// Takes the value out of the entry, and returns it.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

/// A view into a vacant entry in an `ApproxHashMap`. It is part of the
/// [`Entry`] enum.
pub struct VacantEntry<'a, K, V> {
    hash_map_entry: hash_map::Entry<'a, u64, LinearApproxMap<K, V>>,
    key: K,
    len: &'a mut usize,
}

impl<'a, K, V> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntry`.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns a
    /// mutable reference to it.
    pub fn insert(self, value: V) -> &'a mut V {
        self.insert_entry(value).into_mut()
    }

    /// Sets the value of the entry with the `VacantEntry`'s key, and returns an
    /// `OccupiedEntry`.
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        *self.len += 1;
        let (index, hash_map_entry);
        match self.hash_map_entry {
            hash_map::Entry::Occupied(mut e) => {
                index = e.get_mut().push(self.key, value);
                hash_map_entry = e;
            }
            hash_map::Entry::Vacant(e) => {
                index = 0;
                hash_map_entry =
                    e.insert_entry(LinearApproxMap::new_with_single_entry(self.key, value));
            }
        };
        OccupiedEntry {
            hash_map_entry,
            index,
            len: self.len,
        }
    }
}

impl<K, V, S> Extend<(K, V)> for ApproxHashMap<K, V, S>
where
    K: ApproxHash,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

#[derive(Debug, Clone)]
struct LinearApproxMap<K, V>(SmallVec<[(K, V); 1]>);

impl<K, V> Default for LinearApproxMap<K, V> {
    fn default() -> Self {
        Self(SmallVec::new())
    }
}

impl<K, V> LinearApproxMap<K, V> {
    fn new_with_single_entry(key: K, value: V) -> Self {
        Self(smallvec![(key, value)])
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn unwrap_exactly_one(self) -> (K, V) {
        let msg = "expected exactly one element";
        assert_eq!(self.len(), 1, "{msg}");
        self.0.into_iter().next().expect(msg)
    }
}

impl<K: ApproxHash, V> LinearApproxMap<K, V> {
    fn index_of(&self, key: &K) -> Option<usize> {
        self.0.iter().position(|(k, _)| k.interned_eq(key))
    }
}

impl<K, V> LinearApproxMap<K, V> {
    fn key_value(&self, index: usize) -> &(K, V) {
        &self.0[index]
    }
    fn key(&self, index: usize) -> &K {
        &self.0[index].0
    }
    fn value(&self, index: usize) -> &V {
        &self.0[index].1
    }

    fn value_mut(&mut self, index: usize) -> &mut V {
        &mut self.0[index].1
    }

    fn remove(&mut self, index: usize) -> (K, V) {
        self.0.remove(index)
    }

    fn push(&mut self, key: K, value: V) -> usize {
        let i = self.len();
        self.0.push((key, value));
        i
    }
}

impl<K, V> IntoIterator for LinearApproxMap<K, V> {
    type Item = (K, V);

    type IntoIter = smallvec::IntoIter<[(K, V); 1]>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a LinearApproxMap<K, V> {
    type Item = (&'a K, &'a V);

    type IntoIter = std::iter::Map<std::slice::Iter<'a, (K, V)>, fn(&'a (K, V)) -> (&'a K, &'a V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(k, v)| (k, v))
    }
}

impl<'a, K, V> IntoIterator for &'a mut LinearApproxMap<K, V> {
    type Item = (&'a K, &'a mut V);

    type IntoIter =
        std::iter::Map<std::slice::IterMut<'a, (K, V)>, fn(&'a mut (K, V)) -> (&'a K, &'a mut V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut().map(|(k, v)| (k, v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_hashmap() {
        let mut map = ApproxHashMap::new(Precision::absolute(3)); // bucket size = 0.125
        map.insert([0.1, -3.0], 'a');
        map.insert([0.5, 5.0], 'b');
        map.insert([0.6, 0.2], 'c');
        map.insert([0.15, -3.0], 'd');

        assert_eq!(map.get([-5.12, -3.0]), None);
        assert_eq!(map.get([0.5, -3.0]), None);
        assert_eq!(map.get([0.12, -3.0]), Some(&'d'));
        assert_eq!(map.get([-0.12, -2.9]), Some(&'d'));
        assert_eq!(map.get([-0.12, 2.9]), None);
        assert_eq!(map.get([0.44, 5.0]), Some(&'b'));
        assert_eq!(map.get([0.4, 0.3]), Some(&'c'));
    }
}
