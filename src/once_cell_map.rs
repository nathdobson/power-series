use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

use safe_once::unsync::OnceCell;

pub struct OnceCellMap<K, V>(RefCell<HashMap<K, Rc<OnceCell<V>>>>);

impl<K: Eq + Hash, V: Clone> OnceCellMap<K, V> {
    pub fn new() -> Self {
        OnceCellMap(RefCell::new(HashMap::new()))
    }
    pub fn get_or_init(&self, key: K, value: impl FnOnce() -> V) -> V {
        let entry = self.0.borrow_mut().entry(key).or_default().clone();
        entry.get_or_init(value).clone()
    }
}