use crate::gc::shared::MutContainer;

// #[cfg(not(feature = "triomphe"))]
// use crate::gc::shared::ShareableMut;

#[cfg(not(feature = "sync"))]
use crate::gc::shared::ShareableMut;

use crate::gc::{Shared, SharedMut};
use crate::parser::tryfrom_visitor::TryFromExprKindForSteelVal;
use crate::rvals::cycles::BreadthFirstSearchSteelValVisitor;
use crate::rvals::{
    into_serializable_value, Result, SerializableSteelVal, SerializationContext, SteelVal,
};
use crate::values::closed::MarkAndSweepContext;

use crate::parser::{
    ast::ExprKind,
    parser::{ParseError, Parser},
};

use alloc::sync::Arc;

use arc_swap::ArcSwap;
use rustc_hash::FxHashMap;
// TODO add the serializing and deserializing for constants
use serde::{Deserialize, Serialize};
use steel_parser::parser::{lower_entire_ast, SourceId};

// Shared constant map - for repeated in memory execution of a program, this is going to share the same
// underlying representation.
#[derive(Debug)]
pub struct ConstantMap {
    index: SharedMut<ConstantIndex>,
    values: SharedMut<Vec<SteelVal>>,
    // TODO: Flush to these values after a compilation. - maybe have two of them to
    reified_values: Arc<ArcSwap<Vec<SteelVal>>>,
}

#[derive(Debug, Clone, Default)]
struct ConstantIndex {
    nodes: Vec<CanonicalConstant>,
    keys: FxHashMap<ConstantKey, usize>,
    pairs: FxHashMap<usize, usize>,
    #[cfg(test)]
    pair_lookups: usize,
}

#[derive(Debug, Clone)]
struct CanonicalConstant {
    value: SteelVal,
    constant_index: Option<usize>,
}

// Child IDs avoid hashing an entire pair suffix each time its parent is interned.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ConstantKey {
    Atom(SteelVal),
    Pair(usize, usize),
    List(Vec<usize>),
    Vector(Vec<usize>),
}

enum ConstantWork {
    Visit(SteelVal),
    Pair(crate::gc::Gc<crate::values::lists::Pair>),
    List(crate::values::lists::List<SteelVal>),
    Vector(crate::rvals::SteelVector),
}

impl ConstantIndex {
    fn intern(&mut self, value: SteelVal, mut values: Option<&mut Vec<SteelVal>>) -> usize {
        // Atoms need no traversal, which keeps runtime symbol interning to one lookup.
        if !matches!(
            value,
            SteelVal::Pair(_) | SteelVal::ListV(_) | SteelVal::VectorV(_)
        ) {
            let key = ConstantKey::Atom(value.clone());
            let id = match self.keys.get(&key) {
                Some(&id) => id,
                None => self.insert_node(key, value),
            };
            self.publish(id, values);
            return id;
        }
        let mut work = vec![ConstantWork::Visit(value)];
        let mut children = Vec::new();
        while let Some(item) = work.pop() {
            let (key, original) = match item {
                ConstantWork::Visit(SteelVal::Pair(pair)) => {
                    if let Some(&id) = self.pairs.get(&(pair.as_ptr() as usize)) {
                        self.publish(id, values.as_deref_mut());
                        children.push(id);
                        continue;
                    }
                    let car = pair.car();
                    let cdr = pair.cdr();
                    work.push(ConstantWork::Pair(pair));
                    work.push(ConstantWork::Visit(cdr));
                    work.push(ConstantWork::Visit(car));
                    continue;
                }
                ConstantWork::Visit(SteelVal::ListV(list)) => {
                    work.push(ConstantWork::List(list.clone()));
                    let start = work.len();
                    work.extend(list.iter().cloned().map(ConstantWork::Visit));
                    work[start..].reverse();
                    continue;
                }
                ConstantWork::Visit(SteelVal::VectorV(vector)) => {
                    work.push(ConstantWork::Vector(vector.clone()));
                    work.extend(vector.iter().rev().cloned().map(ConstantWork::Visit));
                    continue;
                }
                ConstantWork::Visit(value) => (ConstantKey::Atom(value), None),
                ConstantWork::Pair(pair) => {
                    let cdr = children.pop().unwrap();
                    let car = children.pop().unwrap();
                    #[cfg(test)]
                    {
                        self.pair_lookups += 1;
                    }
                    (ConstantKey::Pair(car, cdr), Some(SteelVal::Pair(pair)))
                }
                ConstantWork::List(list) => (
                    ConstantKey::List(children.split_off(children.len() - list.len())),
                    Some(SteelVal::ListV(list)),
                ),
                ConstantWork::Vector(vector) => (
                    ConstantKey::Vector(children.split_off(children.len() - vector.len())),
                    Some(SteelVal::VectorV(vector)),
                ),
            };
            let id = if let Some(&id) = self.keys.get(&key) {
                id
            } else {
                let value = match &key {
                    ConstantKey::Atom(value) => value.clone(),
                    ConstantKey::Pair(car, cdr) => {
                        let car = &self.nodes[*car].value;
                        let cdr = &self.nodes[*cdr].value;
                        let SteelVal::Pair(pair) = original.unwrap() else {
                            unreachable!()
                        };
                        if pair.car_ref().ptr_eq(car) && pair.cdr_ref().ptr_eq(cdr) {
                            SteelVal::Pair(pair)
                        } else {
                            crate::values::lists::Pair::cons(car.clone(), cdr.clone()).into()
                        }
                    }
                    ConstantKey::List(ids) => {
                        let SteelVal::ListV(list) = original.unwrap() else {
                            unreachable!()
                        };
                        if list
                            .iter()
                            .zip(ids)
                            .all(|(value, id)| value.ptr_eq(&self.nodes[*id].value))
                        {
                            SteelVal::ListV(list)
                        } else {
                            SteelVal::ListV(
                                ids.iter().map(|id| self.nodes[*id].value.clone()).collect(),
                            )
                        }
                    }
                    ConstantKey::Vector(ids) => {
                        let SteelVal::VectorV(vector) = original.unwrap() else {
                            unreachable!()
                        };
                        if vector
                            .iter()
                            .zip(ids)
                            .all(|(value, id)| value.ptr_eq(&self.nodes[*id].value))
                        {
                            SteelVal::VectorV(vector)
                        } else {
                            SteelVal::VectorV(
                                ids.iter().map(|id| self.nodes[*id].value.clone()).collect(),
                            )
                        }
                    }
                };
                self.insert_node(key, value)
            };
            self.publish(id, values.as_deref_mut());
            children.push(id);
        }
        children.pop().unwrap()
    }

    fn insert_node(&mut self, key: ConstantKey, value: SteelVal) -> usize {
        let id = self.nodes.len();
        if let SteelVal::Pair(pair) = &value {
            self.pairs.insert(pair.as_ptr() as usize, id);
        }
        self.nodes.push(CanonicalConstant {
            value,
            constant_index: None,
        });
        self.keys.insert(key, id);
        id
    }

    fn publish(&mut self, id: usize, values: Option<&mut Vec<SteelVal>>) {
        if let Some(values) = values {
            let node = &mut self.nodes[id];
            if node.constant_index.is_none() {
                node.constant_index = Some(values.len());
                values.push(node.value.clone());
            }
        }
    }

    fn rebuild(values: &mut [SteelVal]) -> Self {
        let mut index = Self::default();
        for (position, value) in values.iter_mut().enumerate() {
            let id = index.intern(value.clone(), None);
            let node = &mut index.nodes[id];
            *value = node.value.clone();
            node.constant_index = Some(position);
        }
        index
    }
}

#[derive(Serialize, Deserialize)]
pub struct SerializableConstantMap(Vec<u8>);

impl Default for ConstantMap {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for ConstantMap {
    fn clone(&self) -> Self {
        Self {
            values: Shared::clone(&self.values),
            index: Shared::clone(&self.index),
            reified_values: Arc::clone(&self.reified_values),
        }
    }
}

impl ConstantMap {
    pub fn new() -> ConstantMap {
        ConstantMap {
            values: Shared::new(MutContainer::new(Vec::new())),
            index: Shared::new(MutContainer::new(ConstantIndex::default())),
            // Does this help at all?
            reified_values: Arc::new(ArcSwap::from_pointee(Vec::new())),
        }
    }

    pub fn flush(&self) {
        let values = self.values.read();
        if values.len() != self.reified_values.load().len() {
            self.reified_values.store(Arc::new(values.clone()));
        }
    }

    pub(crate) fn trace(&self, context: &mut MarkAndSweepContext) {
        for value in self.values.read().iter() {
            context.push_back(value.clone());
        }
    }

    pub fn deep_clone(&self) -> ConstantMap {
        let index = self.index.read();
        let values = self.values.read();
        Self {
            index: Shared::new(MutContainer::new(index.clone())),
            values: Shared::new(MutContainer::new(values.clone())),
            reified_values: Arc::new(ArcSwap::from_pointee(values.clone())),
        }
    }

    pub(crate) fn into_serializable_map(self) -> SerializableConstantMap {
        SerializableConstantMap(self.to_bytes().unwrap())
    }

    pub fn to_serializable_vec(&self, ctx: &mut SerializationContext) -> Vec<SerializableSteelVal> {
        self.values
            .read()
            .iter()
            .cloned()
            .map(|x| into_serializable_value(x, ctx))
            .collect::<Result<_>>()
            .unwrap()
    }

    pub fn from_vec(mut vec: Vec<SteelVal>) -> ConstantMap {
        let index = ConstantIndex::rebuild(&mut vec);
        ConstantMap {
            index: Shared::new(MutContainer::new(index)),
            values: Shared::new(MutContainer::new(vec.clone())),
            reified_values: Arc::new(ArcSwap::from_pointee(vec)),
        }
    }

    fn to_constant_expr_map(&self) -> Vec<String> {
        self.values
            .read()
            .iter()
            .map(|x| match x {
                SteelVal::StringV(s) => {
                    format!("{:?}", s)
                }
                SteelVal::CharV(c) => {
                    format!("#\\{c}")
                }
                _ => x.to_string(),
            })
            .collect()
    }

    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        let str_vector = self.to_constant_expr_map();
        // println!("{:?}", str_vector);
        let result = bincode::serialize(&str_vector);

        Ok(result.unwrap())
    }

    pub fn from_serialized(map: SerializableConstantMap) -> Result<Self> {
        Self::from_bytes(&map.0)
    }

    pub fn from_bytes(encoded: &[u8]) -> Result<ConstantMap> {
        let str_vector: Vec<String> = bincode::deserialize(encoded).unwrap();

        str_vector
            .into_iter()
            .map(|x| {
                // Parse the input
                let parsed: core::result::Result<Vec<ExprKind>, ParseError> =
                    Parser::new_flat(&x, SourceId::none()).collect();
                let mut parsed = parsed?;

                lower_entire_ast(&mut parsed[0])?;

                // println!("{}", &parsed[0]);

                TryFromExprKindForSteelVal::try_from_expr_kind(parsed[0].clone())

                // Ok(SteelVal::try_from(parsed[0].clone()).unwrap())
            })
            .collect::<Result<Vec<_>>>()
            .map(Self::from_vec)
    }

    // pub fn from_bytes(encoded: &[u8]) -> ConstantMap {
    //     bincode::deserialize(encoded).unwrap()
    // }
}

impl ConstantMap {
    pub fn add(&mut self, val: SteelVal) -> usize {
        let mut index = self.index.write();
        let mut values = self.values.write();
        let id = index.intern(val, None);
        let idx = values.len();
        index.nodes[id].constant_index = Some(idx);
        values.push(index.nodes[id].value.clone());
        idx
    }

    // Fallible
    #[inline(always)]
    pub fn get(&self, idx: usize) -> SteelVal {
        // Just check if the values are the same. Otherwise, push down to the proper one?

        // if let Some(value) = self.local_values.get(idx) {
        //     return value.clone();
        // } else {
        //     self.local_values = self.reified_values.load().to_vec();
        //     self.local_values[idx].clone()
        // }

        self.values.read()[idx].clone()
    }

    pub fn get_value(&self, idx: usize) -> SteelVal {
        self.reified_values.load()[idx].clone()
        // self.values.read()[idx].clone()
    }

    pub fn get_map<T>(&self, idx: usize, func: impl FnOnce(&SteelVal) -> T) -> T {
        // let value = &self.values.read()[idx];
        let value = &self.reified_values.load()[idx];
        func(value)
    }

    pub fn try_get(&self, idx: usize) -> Option<SteelVal> {
        self.values.read().get(idx).cloned()
    }

    pub fn add_or_get(&mut self, val: SteelVal) -> usize {
        let mut index = self.index.write();
        let id = index.intern(val, Some(&mut self.values.write()));
        index.nodes[id].constant_index.unwrap()
    }

    pub fn len(&self) -> usize {
        self.values.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.read().is_empty()
    }

    pub fn roll_back(&mut self, idx: usize) {
        let mut index = self.index.write();
        let mut values = self.values.write();
        values.truncate(idx);
        *index = ConstantIndex::rebuild(&mut values);
        self.reified_values.store(Arc::new(values.clone()));
    }

    #[cfg(test)]
    pub fn clear(&mut self) {
        self.roll_back(0);
    }
}

#[cfg(test)]
pub mod constant_table_tests {
    use super::*;
    use crate::values::lists::Pair;

    #[test]
    fn long_dotted_list_interns_suffixes_in_linear_work() {
        let mut instance = ConstantMap::new();
        let value = || {
            (0..30_000).fold(SteelVal::IntV(2), |tail, _| {
                Pair::cons(SteelVal::IntV(1), tail).into()
            })
        };
        let idx = instance.add_or_get(value());
        assert_eq!(instance.len(), 30_002);
        assert_eq!(instance.index.read().pair_lookups, 30_000);
        assert_eq!(instance.add_or_get(value()), idx);
        assert_eq!(instance.index.read().pair_lookups, 60_000);

        let value = instance.get(idx);
        let mut tail = &value;
        for _ in 0..30_000 {
            let pair = tail.pair().expect("expected another pair");
            assert_eq!(pair.car_ref(), &SteelVal::IntV(1));
            tail = pair.cdr_ref();
        }
        assert_eq!(tail, &SteelVal::IntV(2));
        assert_eq!(instance.add_or_get(value), idx);
        assert_eq!(instance.len(), 30_002);
        assert_eq!(instance.index.read().pair_lookups, 60_000);
    }

    #[test]
    fn pair_elements_and_tail_use_canonical_constants() {
        let mut instance = ConstantMap::new();
        let string = || SteelVal::StringV("shared".into());
        let vector = || SteelVal::VectorV([string()].into_iter().collect());
        let list = || SteelVal::ListV([string()].into_iter().collect());
        let string_idx = instance.add_or_get(string());
        let vector_idx = instance.add_or_get(vector());
        let list_idx = instance.add_or_get(list());

        let value = Pair::cons(vector(), Pair::cons(string(), list()).into()).into();
        let idx = instance.add_or_get(value);
        let value = instance.get(idx);
        let first = value.pair().unwrap();
        assert!(first.car_ref().ptr_eq(&instance.get(vector_idx)));
        let second = first.cdr_ref().pair().unwrap();
        assert!(second.car_ref().ptr_eq(&instance.get(string_idx)));
        assert!(second.cdr_ref().ptr_eq(&instance.get(list_idx)));
        assert_eq!(instance.len(), 5);
    }

    #[test]
    fn suffix_identity_survives_insertion_cloning_and_reconstruction() {
        let suffix = || SteelVal::from(Pair::cons(SteelVal::IntV(2), SteelVal::IntV(3)));
        let whole = || SteelVal::from(Pair::cons(SteelVal::IntV(1), suffix()));
        for suffix_first in [false, true] {
            for direct in [false, true] {
                let mut map = ConstantMap::new();
                let mut insert = |value| {
                    if direct {
                        map.add(value)
                    } else {
                        map.add_or_get(value)
                    }
                };
                let (whole_idx, suffix_idx) = if suffix_first {
                    let suffix_idx = insert(suffix());
                    (insert(whole()), suffix_idx)
                } else {
                    let whole_idx = insert(whole());
                    (whole_idx, insert(suffix()))
                };
                let bytes = map.to_bytes().unwrap();
                let rebuilt = ConstantMap::from_vec(map.values.read().clone());
                for mut copy in [
                    map.clone(),
                    map.deep_clone(),
                    rebuilt,
                    ConstantMap::from_bytes(&bytes).unwrap(),
                ] {
                    assert_eq!(copy.to_bytes().unwrap(), bytes);
                    assert!(copy
                        .get(whole_idx)
                        .pair()
                        .unwrap()
                        .cdr_ref()
                        .ptr_eq(&copy.get(suffix_idx)));
                    assert_eq!(copy.add_or_get(whole()), whole_idx);
                    assert_eq!(copy.add_or_get(suffix()), suffix_idx);
                    assert!(copy
                        .get(whole_idx)
                        .pair()
                        .unwrap()
                        .cdr_ref()
                        .ptr_eq(&copy.get(suffix_idx)));
                }
            }
        }
    }

    #[test]
    fn rollback_and_clear_rebuild_all_indexes_and_flushed_values() {
        let mut map = ConstantMap::new();
        let value = || SteelVal::from(Pair::cons(SteelVal::IntV(1), SteelVal::IntV(2)));
        map.add(SteelVal::IntV(42));
        let mut shared = map.clone();
        map.add_or_get(value());
        map.flush();
        map.roll_back(1);
        assert_eq!(shared.len(), 1);
        assert_eq!(shared.reified_values.load().len(), 1);
        assert_eq!(shared.add_or_get(value()), 3);
        assert_eq!(map.len(), 4);
        let mut independent = map.deep_clone();
        map.clear();
        assert!(shared.is_empty());
        assert!(shared.reified_values.load().is_empty());
        assert_eq!(map.add_or_get(value()), 2);
        assert_eq!(independent.add_or_get(value()), 3);
    }

    #[cfg(not(feature = "without-drop-protection"))]
    #[test]
    fn nested_constants_intern_and_drop_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                #[cfg(all(feature = "sync", feature = "biased"))]
                steel_rc::register_thread();
                for shape in 0..4 {
                    let mut map = ConstantMap::new();
                    let make_value = || {
                        (0..10_000).fold(SteelVal::IntV(0), |child, depth| match shape {
                            0 => Pair::cons(child, SteelVal::IntV(1)).into(),
                            1 => Pair::cons(SteelVal::IntV(1), child).into(),
                            2 if depth % 2 == 0 => Pair::cons(child, SteelVal::IntV(1)).into(),
                            2 => Pair::cons(SteelVal::IntV(1), child).into(),
                            _ if depth % 2 == 0 => SteelVal::ListV([child].into_iter().collect()),
                            _ => SteelVal::VectorV([child].into_iter().collect()),
                        })
                    };
                    let idx = map.add_or_get(make_value());
                    assert_eq!(map.add_or_get(make_value()), idx);
                    assert_eq!(map.deep_clone().add_or_get(map.get(idx)), idx);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn run_tests_constant_map() {
        let mut instance = ConstantMap::new();
        test_add(&mut instance);

        let mut instance = ConstantMap::new();
        test_get(&mut instance);
    }

    fn test_add(instance: &mut ConstantMap) {
        assert_eq!(instance.len(), 0);
        let val1 = SteelVal::BoolV(true);
        let val2 = SteelVal::BoolV(false);
        assert_eq!(instance.add(val1), 0);
        assert_eq!(instance.add(val2), 1);
    }

    fn test_get(instance: &mut ConstantMap) {
        assert_eq!(instance.len(), 0);
        let val1 = SteelVal::BoolV(true);
        let val2 = SteelVal::BoolV(false);
        assert_eq!(instance.add(val1), 0);
        assert_eq!(instance.add(val2), 1);

        assert_eq!(instance.get(0), SteelVal::BoolV(true));
        assert_eq!(instance.get(1), SteelVal::BoolV(false));
    }
}
