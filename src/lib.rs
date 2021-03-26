use std::{
    cell::UnsafeCell,
    collections::HashMap,
    ops::{Deref, DerefMut},
    sync::{Arc, Weak},
};

use node_list::NodeList;
use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};

mod node_list;
mod persist;
mod serialiser;

pub struct PersistXml {
    mapped_initialisers: HashMap<
        String,
        fn(node_data: NodeData, xml_element_data: XmlElementData) -> Arc<dyn XmlElement>,
    >,
}

pub struct Builder {
    mapped_initialisers: HashMap<
        String,
        fn(node_data: NodeData, xml_element_data: XmlElementData) -> Arc<dyn XmlElement>,
    >,
}

fn test() {
    let p = Builder::new()
        .map_elem::<BaseXmlElement>("te")
        .map_custom_init("test", BaseXmlElement::init_xml_element)
        .build();
}

impl Builder {
    pub fn new() -> Self {
        Builder {
            mapped_initialisers: HashMap::new(),
        }
    }

    pub fn map_elem<T: XmlElement>(mut self, tag_name: &str) -> Builder {
        self.mapped_initialisers
            .insert(String::from(tag_name), T::init_xml_element);
        self
    }

    pub fn map_custom_init(
        mut self,
        tag_name: &str,
        init_fn: fn(node_data: NodeData, xml_element_data: XmlElementData) -> Arc<dyn XmlElement>,
    ) -> Builder {
        self.mapped_initialisers
            .insert(String::from(tag_name), init_fn);
        self
    }

    pub fn build(self) -> PersistXml {
        PersistXml {
            mapped_initialisers: self.mapped_initialisers,
        }
    }
}

impl Default for Builder {
    fn default() -> Self {
        Builder::new()
    }
}

pub enum Node {
    XmlElement(Arc<dyn XmlElement>),
    Text(Arc<TextNode>),
}

impl Clone for Node {
    fn clone(&self) -> Self {
        match self {
            Self::XmlElement(elem) => Self::XmlElement(Arc::clone(elem)),
            Self::Text(text) => Self::Text(Arc::clone(text)),
        }
    }
}

impl Node {
    pub fn try_borrow_mut(&mut self) -> Option<NodeRefMut<'_>> {
        match self {
            Self::XmlElement(elem) => {
                Arc::get_mut(elem).map(|mut_ref| NodeRefMut::XmlElement(mut_ref))
            }
            Self::Text(text) => Arc::get_mut(text).map(|mut_ref| NodeRefMut::Text(mut_ref)),
        }
    }

    pub fn get_node_data(&self) -> &NodeData {
        match self {
            Self::XmlElement(elem) => elem.get_node_data(),
            Self::Text(text) => &text.node_data,
        }
    }

    pub fn downgrade(&self) -> NodeWeak {
        match self {
            Self::XmlElement(elem) => NodeWeak::XmlElement(Arc::downgrade(elem)),
            Self::Text(text) => NodeWeak::Text(Arc::downgrade(text)),
        }
    }
}

pub enum NodeReadGuard<'a> {
    XmlElement(RwLockReadGuard<'a, dyn XmlElement>),
    Text(RwLockReadGuard<'a, TextNode>),
}

impl NodeReadGuard<'_> {
    pub fn get_node_data(&self) -> &NodeData {
        match self {
            Self::XmlElement(elem) => elem.get_node_data(),
            Self::Text(text) => &text.node_data,
        }
    }
}

pub enum NodeWriteGuard<'a> {
    XmlElement(RwLockWriteGuard<'a, dyn XmlElement>),
    Text(RwLockWriteGuard<'a, TextNode>),
}

impl NodeWriteGuard<'_> {
    pub fn get_node_data_mut(&mut self) -> &mut NodeData {
        match self {
            Self::XmlElement(elem) => elem.get_node_data_mut(),
            Self::Text(text) => &mut text.node_data,
        }
    }
}

pub enum NodeRefMut<'a> {
    XmlElement(&'a mut dyn XmlElement),
    Text(&'a mut TextNode),
}

impl NodeRefMut<'_> {
    pub fn get_node_data_mut(&mut self) -> &mut NodeData {
        match self {
            Self::XmlElement(elem) => elem.get_node_data_mut(),
            Self::Text(text) => &mut text.node_data,
        }
    }
}

pub enum NodeWeak {
    XmlElement(Weak<dyn XmlElement>),
    Text(Weak<TextNode>),
}

impl Clone for NodeWeak {
    fn clone(&self) -> Self {
        match self {
            Self::XmlElement(elem) => Self::XmlElement(Weak::clone(elem)),
            Self::Text(text) => Self::Text(Weak::clone(text)),
        }
    }
}

impl NodeWeak {
    pub fn try_upgrade(&self) -> Option<Node> {
        match self {
            Self::XmlElement(weak) => weak.upgrade().map(|strong| Node::XmlElement(strong)),
            Self::Text(weak) => weak.upgrade().map(|strong| Node::Text(strong)),
        }
    }

    pub fn upgrade(&self) -> Node {
        self.try_upgrade()
            .expect("could not upgrade weak reference to node")
    }
}

pub trait XmlElement: Send + Sync {
    fn init_xml_element(
        node_data: NodeData,
        xml_element_data: XmlElementData,
    ) -> Arc<dyn XmlElement>
    where
        Self: Sized;

    fn get_node_data(&self) -> &NodeData;

    fn get_node_data_mut(&mut self) -> &mut NodeData;

    fn get_xml_element_data(&self) -> &XmlElementData;

    fn get_xml_element_data_mut(&mut self) -> &mut XmlElementData;

    fn is_sub_element(&self) -> bool {
        let node_data = self.get_node_data();
        // TODO impl
        false
    }

    fn get_tag_name(&self) -> &str {
        &self.get_xml_element_data().tag_name
    }
}

pub struct BaseXmlElement {
    node_data: NodeData,
    xml_element_data: XmlElementData,
}

impl XmlElement for BaseXmlElement {
    fn init_xml_element(
        node_data: NodeData,
        xml_element_data: XmlElementData,
    ) -> Arc<dyn XmlElement> {
        Arc::new(BaseXmlElement {
            node_data,
            xml_element_data,
        })
    }

    fn get_node_data(&self) -> &NodeData {
        &self.node_data
    }

    fn get_node_data_mut(&mut self) -> &mut NodeData {
        &mut self.node_data
    }

    fn get_xml_element_data(&self) -> &XmlElementData {
        &self.xml_element_data
    }

    fn get_xml_element_data_mut(&mut self) -> &mut XmlElementData {
        &mut self.xml_element_data
    }
}

pub struct TextNode {
    node_data: NodeData,
    text: String,
}

pub struct NodeData {
    inner: UnsafeCell<NodeDataInner>,
    lock: UnsafeCell<Arc<RwLock<()>>>,
    // Secondary lock to protect critical sections where the main lock is swapped.
    // See `swap_locks` and `acquire_read_lock` / `acquire_write_lock`
    lock_swap_protection: RwLock<()>,
}

// access to the cell is thread-safe as it is managed by the lock
unsafe impl Send for NodeData {}
unsafe impl Sync for NodeData {}

impl NodeData {
    pub fn get_mut(&mut self) -> &mut NodeDataInner {
        self.inner.get_mut()
    }

    pub fn read(&self) -> NodeDataReadGuard<'_> {
        let guard = self.acquire_read_lock();

        // SAFETY:
        // getting a shared reference to the data is safe
        // since the read lock has been acquired
        let inner = unsafe { &*self.inner.get() };

        NodeDataReadGuard {
            _guard: guard,
            inner,
        }
    }

    pub fn write(&self) -> NodeDataWriteGuard<'_> {
        let guard = self.acquire_write_lock();

        // SAFETY:
        // getting an exclusive reference to the data is safe
        // since the write lock has been acquired
        let inner = unsafe { &mut *self.inner.get() };

        NodeDataWriteGuard {
            _guard: guard,
            inner,
        }
    }

    /// Get a shared reference to the `NodeDataInner` without acquiring a lock.
    /// Useful when the caller manages the lock.
    ///
    /// SAFETY:
    /// This function is only safe to call if the caller holds the read lock of this
    /// NodeData's lock for the entire duration of the borrow.
    pub unsafe fn force_read(&self) -> &NodeDataInner {
        &*self.inner.get()
    }

    /// Get an exclusive reference to the `NodeDataInner` without acquiring a lock.
    /// Useful when the caller manages the lock.
    ///
    /// SAFETY:
    /// This function is only safe to call if the caller holds the write lock of this
    /// NodeData's lock for the entire duration of the borrow.
    pub unsafe fn force_write(&self) -> &mut NodeDataInner {
        &mut *self.inner.get()
    }

    /// Swaps the current main lock of this NodeData for the provided lock. First acquires write access
    /// to the `lock_swap_protection` lock to safely get a mutable reference to the current lock, then
    /// acquires write access to the current lock to wait for current readers of the lock to finish before
    /// swapping the lock for the provided lock. Then acquires and returns write access to the new lock.
    /// This function holds two locks at the same time (`lock_swap_protection` and the current lock,
    /// then `lock_swap_protection` and the new lock) but guarantees to not cause any deadlocks since
    /// this function and `acquire_lock()` are the only places where these locks overlap and no thread
    /// tries to acquire the `lock_swap_protection` lock while holding the main lock of a NodeData.
    ///
    /// This function is used when a Node is inserted to or removed from a NodeList to adopt or remove
    /// the lock of the NodeList.
    ///
    /// The contract for this function is that the caller does not already hold the lock for this NodeData.
    pub(crate) fn swap_and_acquire_lock(
        &self,
        new_lock: Arc<RwLock<()>>,
    ) -> RwLockWriteGuard<'_, ()> {
        let _swap_protection_guard = self.lock_swap_protection.write();
        // SAFETY:
        // Exclusive access to the lock is safe because the current thread holds write access to the
        // `lock_swap_protection` lock.
        let lock = unsafe { &mut *self.lock.get() };
        let curr_lock = Arc::clone(lock);
        // no deadlock: the current owner of the lock is not waiting for access to the `lock_swap_protection`
        // lock because in the only places where the locks overlap (this function and `acquire_lock()`) the
        // `lock_swap_protection` lock is always acquired first.
        let curr_lock_guard = curr_lock.write();
        // The current thread acquires write access to the current lock to assure that all readers using the lock
        // are done before swapping the locks.
        *lock = new_lock;
        drop(curr_lock_guard);

        // no deadlock: the only other lock currently held is still the `lock_swap_protection` lock as
        // the previous lock has been released, so the same argument applies.
        lock.write()
    }

    pub(crate) fn acquire_read_lock(&self) -> RwLockReadGuard<'_, ()> {
        self.acquire_lock(RwLock::read)
    }

    pub(crate) fn acquire_write_lock(&self) -> RwLockWriteGuard<'_, ()> {
        self.acquire_lock(RwLock::write)
    }

    /// Acquire the main lock of this `NodeData` to gain access to the inner NodeData.
    /// This first acquires read access to the `lock_swap_protection` to make sure that no other thread
    /// may swap the main lock in the meantime. The `lock_swap_protection` lock is released when this
    /// function goes out of scope and the guard (read or write) for the main lock is returned to the caller.
    /// Since swapping the main lock in `swap_and_acquire_lock` acquires both the `lock_swap_protection` lock
    /// and the current main lock, the main lock is guaranteed not to be swapped while the caller holds the
    /// guard.
    fn acquire_lock<'a, T: 'a>(&self, lock_supplier: fn(&'a RwLock<()>) -> T) -> T {
        let _swap_protection_guard = self.lock_swap_protection.read();
        // SAFETY:
        // Acquiring a shared reference to the main lock is safe because the current thread has read access
        // to the `lock_swap_protection` lock and an exclusive reference to the lock is only given out
        // in `swap_and_acquire_lock` while holding write access to the `lock_swap_protection` lock, so the lock
        // ensures there can never be a reader while there is a writer thus Rust's reference rules are met.
        let lock = unsafe { &*self.lock.get() };
        lock_supplier(lock)
    }
}

pub enum NodeDataInner {
    Init(NodeDataInit),
    Detached,
}

impl NodeDataInner {
    pub fn is_detached(&self) -> bool {
        match self {
            Self::Init(_) => false,
            Self::Detached => true,
        }
    }

    pub fn prev_sibling(&self) -> Option<Node> {
        match self {
            Self::Init(data) => {
                if let Some(ref prev) = data.prev_sibling {
                    Some(prev.upgrade())
                } else {
                    None
                }
            }
            Self::Detached => None,
        }
    }

    fn set_prev_sibling(&mut self, prev_sibling: NodeWeak) {
        let data = self.get_or_init_data();
        data.prev_sibling = Some(prev_sibling);
    }

    fn unset_prev_sibling(&mut self) {
        let data = self.get_or_init_data();
        data.prev_sibling = None;
    }

    pub fn next_sibling(&self) -> Option<Node> {
        match self {
            Self::Init(data) => {
                if let Some(ref next) = data.next_sibling {
                    Some(next.clone())
                } else {
                    None
                }
            }
            Self::Detached => None,
        }
    }

    fn set_next_sibling(&mut self, next_sibling: Node) {
        let data = self.get_or_init_data();
        data.next_sibling = Some(next_sibling);
    }

    fn unset_next_sibling(&mut self) {
        let data = self.get_or_init_data();
        data.next_sibling = None;
    }

    #[inline]
    fn get_or_init_data(&mut self) -> &mut NodeDataInit {
        match self {
            Self::Init(ref mut data) => data,
            Self::Detached => {
                let data = NodeDataInit::default();
                *self = Self::Init(data);
                match self {
                    Self::Init(ref mut data) => data,
                    Self::Detached => unreachable!(),
                }
            }
        }
    }
}

#[derive(Default)]
pub struct NodeDataInit {
    parent: Option<Weak<dyn XmlElement>>,
    next_sibling: Option<Node>,
    prev_sibling: Option<NodeWeak>,
}

pub struct NodeDataReadGuard<'a> {
    _guard: RwLockReadGuard<'a, ()>,
    inner: &'a NodeDataInner,
}

impl Deref for NodeDataReadGuard<'_> {
    type Target = NodeDataInner;

    fn deref(&self) -> &<Self as Deref>::Target {
        self.inner
    }
}

pub struct NodeDataWriteGuard<'a> {
    _guard: RwLockWriteGuard<'a, ()>,
    inner: &'a mut NodeDataInner,
}

impl Deref for NodeDataWriteGuard<'_> {
    type Target = NodeDataInner;

    fn deref(&self) -> &<Self as Deref>::Target {
        self.inner
    }
}

impl DerefMut for NodeDataWriteGuard<'_> {
    fn deref_mut(&mut self) -> &mut <Self as Deref>::Target {
        self.inner
    }
}

pub struct XmlElementData {
    tag_name: String,
    children: NodeList,
    attributes: HashMap<String, XmlAttribute>,
}

pub struct XmlAttribute {
    str_val: String,
}

#[cfg(test)]
mod tests {

    use std::sync::Arc;

    use crate::{persist::context::Context, Builder, Node, XmlElement};
    use std::ops::Deref;

    #[test]
    fn it_works() {
        let backend = Builder::new().build();
        let context = Context::create_for_str(
            &backend,
            r#"
        <root>
          <sub1>
            <sub11/>
            <sub12>
              <sub121/>
              <sub122/>
            </sub12>
            <sub13/>
          </sub1>
          <sub2/>
        </root>
        "#,
        );

        fn print_children(elem: &Arc<dyn XmlElement>, level: usize) {
            let xml_element_data = elem.get_xml_element_data();
            let node_data_lock = unsafe { &*elem.get_node_data().lock.get() }.deref();
            let node_list_lock = xml_element_data.children.lock.deref();
            let tag_name = &xml_element_data.tag_name;
            let padding = String::from(" ").repeat(level * 2);
            eprintln!(
                "{}<{}>; NodeData lock {:p}, NodeList lock {:p}",
                padding, tag_name, node_data_lock, node_list_lock
            );

            for child in xml_element_data.children.iter() {
                match child {
                    Node::XmlElement(elem) => {
                        print_children(&elem, level + 1);
                    }
                    _ => {}
                }
            }
        }

        print_children(&context.root_element(), 0);

        assert_eq!(2 + 2, 4);
    }
}
