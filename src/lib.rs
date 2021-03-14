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

    /// SAFETY:
    /// It is only safe to call this function while holding write access to the current main lock.
    /// This function acquires the `lock_swap_protection` lock to ensure that no other threads
    /// are trying to dereference the cell which contains the main lock but this function still
    /// requires the caller to have write access to the main lock because otherwise there might
    /// be threads using the current lock. This does not cause a deadlock since write access to
    /// the `lock_swap_protection` lock is only acquired here while holding write access to the main
    /// lock and read access to the `lock_swap_protection` lock is only acquired by the
    /// `acquire_read_lock` and `acquire_write_lock` functions, where the `lock_swap_protection` lock
    /// is released before acquiring the main lock, so readers never hold both locks at the same time
    /// and no other writers exist. The important thing is that no thread tries to acquire the main
    /// lock while still holding the `lock_swap_protection` lock.
    pub(crate) unsafe fn swap_locks(&self, new_lock: Arc<RwLock<()>>) {
        let _guard = self.lock_swap_protection.write();
        let lock = &mut *self.lock.get();
        *lock = new_lock;
    }

    pub(crate) fn acquire_read_lock(&self) -> RwLockReadGuard<'_, ()> {
        self.acquire_lock(RwLock::read)
    }

    pub(crate) fn acquire_write_lock(&self) -> RwLockWriteGuard<'_, ()> {
        self.acquire_lock(RwLock::write)
    }

    fn acquire_lock<'a, T: 'a>(&self, lock_supplier: fn(&'a RwLock<()>) -> T) -> T {
        let lock_swap_guard = self.lock_swap_protection.read();
        // SAFETY:
        // Acquiring a shared reference to the main lock is safe because the current thread has read access
        // to the `lock_swap_protection` lock and an exclusive reference to the lock is only given out
        // in `swap_locks` while holding write access to the `lock_swap_protection` lock, so the lock
        // ensures there can never be a reader while there is a writer thus Rust's reference rules are met.
        let mut lock = unsafe { &*self.lock.get() };
        // Clone the Arc that holds the main lock to ensure that it is not deallocated by any writers after
        // the `lock_swap_guard` is released and before this thread acquires read access to the main lock.
        let mut _pinned_lock = Arc::clone(lock);
        // Release the `lock_swap_protection` lock because the lock cannot overlap with the main lock to
        // avoid deadlocks with writers, see `swap_locks()`.
        drop(lock_swap_guard);

        loop {
            let guard = lock_supplier(lock);

            // There is no guarantee that a writer didn't manage to acquire the main lock after this thread
            // released the `lock_swap_protection` lock and before this thread managed to acquire read access
            // to the main lock, so now that the lock has been acquired it has to be checked that the lock is
            // still the current main lock, else the process has to be retried.
            let lock_swap_guard = self.lock_swap_protection.read();
            // SAFETY:
            // Dereferencing main lock is safe because the current thread holds read access to the
            // `lock_swap_protection`.
            let rechecked_lock = unsafe { &*self.lock.get() };

            // lock may have been swapped by the previous holder of the lock
            if Arc::ptr_eq(lock, rechecked_lock) {
                return guard;
            } else {
                // retry acquiring the new lock
                lock = rechecked_lock;
                // keep a clone of the lock to make sure it is not dropped by any writers that may swap locks
                // after releasing the `lock_swap_protection` lock.
                _pinned_lock = Arc::clone(lock);
                drop(lock_swap_guard);
            }
        }
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
