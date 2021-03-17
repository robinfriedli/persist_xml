use std::{
    cell::UnsafeCell,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::{Node, NodeData, NodeDataInner, NodeWeak};

pub struct NodeList {
    pub(crate) head: UnsafeCell<Option<Node>>,
    pub(crate) tail: UnsafeCell<Option<NodeWeak>>,
    pub(crate) len: AtomicUsize,
    pub(crate) lock: Arc<RwLock<()>>,
}

// access to the cell is thread-safe as it is managed by the lock
unsafe impl Send for NodeList {}
unsafe impl Sync for NodeList {}

impl NodeList {
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> NodeListIter {
        let guard = self.lock.read();
        // SAFETY:
        // Access to the cell is safe since the lock has been acquired.
        let head = unsafe { &*self.head.get() };
        NodeListIter {
            next: head.as_ref().map(|head| head.clone()),
            node_list: &self,
            _guard: guard,
        }
    }

    pub fn link_before(&self, node: Node, successor: Node) {
        let (_guard, node_data, successor_node_data) = self.lock_nodes(&node, &successor);

        if let Some(prev_sibling) = successor_node_data.prev_sibling() {
            node_data.set_prev_sibling(prev_sibling.downgrade());

            let prev_sibling_node_data = prev_sibling.get_node_data();
            self.check_current(&prev_sibling_node_data);
            // SAFETY:
            // As asserted using `check_current()`, the prev_sibling Node is protected by this NodeList's lock
            // so access is safe since the current thread holds the write lock.
            let prev_sibling_node_data = unsafe { prev_sibling_node_data.force_write() };
            prev_sibling_node_data.unset_next_sibling();
            prev_sibling_node_data.set_next_sibling(node.clone());
        } else {
            // the node before which the new node is inserted does not have a previous node
            // meaning the new node will be the new head

            // SAFETY:
            // Mutable access to the cell is safe since the write lock has been acquired.
            let head = unsafe { &mut *self.head.get() };
            *head = Some(node.clone());
        }

        node_data.set_next_sibling(successor.clone());
        successor_node_data.unset_prev_sibling();
        successor_node_data.set_prev_sibling(node.downgrade());

        self.len.fetch_add(1, Ordering::Relaxed);
    }

    pub fn link_after(&self, node: Node, predecessor: Node) {
        let (_guard, node_data, predecessor_node_data) = self.lock_nodes(&node, &predecessor);

        if let Some(next_sibling) = predecessor_node_data.next_sibling() {
            node_data.set_next_sibling(next_sibling.clone());

            let next_sibling_node_data = next_sibling.get_node_data();
            self.check_current(&next_sibling_node_data);
            // SAFETY:
            // As asserted using `check_current()`, the next_sibling Node is protected by this NodeList's lock
            // so access is safe since the current thread holds the write lock.
            let next_sibling_node_data = unsafe { next_sibling_node_data.force_write() };
            next_sibling_node_data.unset_prev_sibling();
            next_sibling_node_data.set_prev_sibling(node.downgrade());
        } else {
            // the node after which the new node is inserted does not have a next node
            // meaning the new node will be the new tail

            // SAFETY:
            // Mutable access to the cell is safe since the write lock has been acquired.
            let tail = unsafe { &mut *self.tail.get() };
            *tail = Some(node.downgrade());
        }

        node_data.set_prev_sibling(predecessor.downgrade());
        predecessor_node_data.unset_next_sibling();
        predecessor_node_data.set_next_sibling(node.clone());

        self.len.fetch_add(1, Ordering::Relaxed);
    }

    pub fn link_first(&self, node: Node) {
        let node_data = node.get_node_data();
        let _guard = node_data.swap_and_acquire_lock(self.lock.clone());
        // SAFETY:
        // The lock of the provided Node has been set to the lock of this NodeList
        // using `NodeData::swap_and_acquire_lock()` and the write lock has been acquired.
        let node_data = unsafe { node_data.force_write() };

        // SAFETY:
        // Mutable access to the cell is safe since the write lock has been acquired.
        let head = unsafe { &mut *self.head.get() };

        if let Some(curr_head) = head.take() {
            node_data.set_next_sibling(curr_head.clone());

            let curr_head_node_data = curr_head.get_node_data();
            self.check_current(&curr_head_node_data);
            // SAFETY:
            // As asserted using `check_current()`, the curr_head Node is protected by this NodeList's lock
            // so access is safe since the current thread holds the write lock.
            let curr_head_node_data = unsafe { curr_head_node_data.force_write() };
            curr_head_node_data.unset_prev_sibling();
            curr_head_node_data.set_prev_sibling(node.downgrade());
        } else {
            // NodeList was empty, set new element as both head and tail

            // SAFETY:
            // Mutable access to the cell is safe since the write lock has been acquired.
            let tail = unsafe { &mut *self.tail.get() };
            *tail = Some(node.downgrade());
        }

        *head = Some(node.clone());
        self.len.fetch_add(1, Ordering::Relaxed);
    }

    pub fn link_last(&self, node: Node) {
        let node_data = node.get_node_data();
        let _guard = node_data.swap_and_acquire_lock(self.lock.clone());
        // SAFETY:
        // The lock of the provided Node has been set to the lock of this NodeList
        // using `NodeData::swap_and_acquire_lock()` and the write lock has been acquired.
        let node_data = unsafe { node_data.force_write() };

        // SAFETY:
        // Mutable access to the cell is safe since the write lock has been acquired.
        let tail = unsafe { &mut *self.tail.get() };

        if let Some(curr_tail) = tail.take() {
            node_data.set_prev_sibling(curr_tail.clone());

            let curr_tail = curr_tail.try_upgrade().expect(
                "Could not upgrade weak pointer to list tail, meaning the previous node must have been dropped. Mutating the list while dropping is not safe."
            );

            let curr_tail_node_data = curr_tail.get_node_data();
            self.check_current(&curr_tail_node_data);
            // SAFETY:
            // As asserted using `check_current()`, the curr_tail Node is protected by this NodeList's lock
            // so access is safe since the current thread holds the write lock.
            let curr_tail_node_data = unsafe { curr_tail_node_data.force_write() };
            curr_tail_node_data.unset_next_sibling();
            curr_tail_node_data.set_next_sibling(node.clone());
        } else {
            // NodeList was empty, set new element as both head and tail

            // SAFETY:
            // Mutable access to the cell is safe since the write lock has been acquired.
            let head = unsafe { &mut *self.head.get() };
            *head = Some(node.clone());
        }

        *tail = Some(node.downgrade());
        self.len.fetch_add(1, Ordering::Relaxed);
    }

    fn lock_nodes<'a>(
        &self,
        node: &'a Node,
        other_node: &'a Node,
    ) -> (
        RwLockWriteGuard<'a, ()>,
        &'a mut NodeDataInner,
        &'a mut NodeDataInner,
    ) {
        let node_data = node.get_node_data();
        let guard = node_data.swap_and_acquire_lock(self.lock.clone());
        let other_node_data = other_node.get_node_data();
        self.check_current(&other_node_data);

        // SAFETY:
        // at this point we can be certain that both `node` and `other_node` are
        // protected by this NodeList's lock and we hold the lock
        let node_data = unsafe { node_data.force_write() };
        let other_node_data = unsafe { other_node_data.force_write() };
        (guard, node_data, other_node_data)
    }

    /// Verify that the node is part of this NodeList by asserting that
    /// the lock that protects the node's data is the lock of this NodeList
    #[inline]
    fn check_current(&self, node_data: &NodeData) {
        // SAFETY:
        // This function is used to assert that the lock of the this NodeList
        // (which is held by the current thread) is indeed the same as the lock
        // for the provided `node_data`, this should never be false. So getting
        // the reference to the lock is same as it should be the same as the one
        // held by the current thread anyway.
        let curr_lock = unsafe { &*node_data.lock.get() };
        assert!(
            Arc::ptr_eq(&self.lock, curr_lock),
            "Inconsistent data in NodeList! Either the reference node used during an insertion \
            (predecessor / successor Node) or a sibling Node's lock does not match the lock of the NodeList and can't be accessed safely."
        )
    }
}

pub struct NodeListIter<'a> {
    next: Option<Node>,
    node_list: &'a NodeList,
    _guard: RwLockReadGuard<'a, ()>,
}

impl Iterator for NodeListIter<'_> {
    type Item = Node;

    // TODO create cheaper implementation where the entire NodeList is protected by a single lock
    // and the iterator returns references
    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if let Some(next) = self.next.take() {
            let next_node_data = next.get_node_data();
            self.node_list.check_current(&next_node_data);
            // SAFETY:
            // The `NodeListIter` owns a read guard for the NodeList's lock, which protects all of its Nodes.
            // `check_current()` checks the consistency of the NodeList and that the locks actually matches
            // just to be sure.
            let next_node_data = unsafe { next_node_data.force_read() };
            let after = next_node_data.next_sibling();
            self.next = after;

            Some(next)
        } else {
            None
        }
    }
}
