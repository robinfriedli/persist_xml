use std::{
    cell::UnsafeCell,
    collections::HashMap,
    io::BufRead,
    str::from_utf8,
    sync::{Arc, Weak},
};

use parking_lot::RwLock;
use quick_xml::{
    events::{BytesStart, Event},
    Reader,
};

use crate::{
    node_list::NodeList, BaseXmlElement, Node, NodeData, NodeDataInit, NodeDataInner, NodeWeak,
    PersistXml, TextNode, XmlAttribute, XmlElement, XmlElementData,
};

pub(crate) fn parse_tree<B: BufRead>(
    mut reader: Reader<B>,
    backend: &PersistXml,
) -> Arc<dyn XmlElement> {
    let mut node_drafts = Vec::new();
    let mut buf = Vec::new();

    let mut root = None;

    loop {
        match reader.read_event(&mut buf) {
            Ok(Event::Start(ref elem)) => {
                let node_draft = create_node_draft(elem, &reader);
                node_drafts.push(node_draft);
            }
            Ok(Event::Empty(ref elem)) => {
                let node_draft = create_node_draft(elem, &reader);
                if let Some(parent) = node_drafts.last_mut() {
                    parent.adopt_child(node_draft);
                } else {
                    // it is technically possible for the root element to be one empty element
                    if root.replace(node_draft).is_some() {
                        // TODO error handling
                        panic!("multiple root nodes");
                    }
                }
            }
            Ok(Event::Text(ref text_elem)) => {
                // TODO error handling
                let text_node_draft =
                    NodeDraft::TextNode(text_elem.unescape_and_decode(&reader).unwrap());
                if let Some(parent) = node_drafts.last_mut() {
                    parent.adopt_child(text_node_draft);
                }

                // ignore trailing text before or after root node
                // if this contains anything other than whitespace it is not valid xml anyway
            }
            Ok(Event::End(_)) => {
                let closed_elem = node_drafts
                    .pop()
                    .expect("node_draft stack empty on Event::End event");

                if let Some(last) = node_drafts.last_mut() {
                    last.adopt_child(closed_elem);
                } else {
                    if root.replace(closed_elem).is_some() {
                        // TODO error handling
                        panic!("multiple root nodes");
                    }
                }
            }
            Ok(Event::Eof) => break,
            // TODO error handling
            Err(e) => panic!("quick_xml error {:?}", e),
            _ => {}
        }
    }

    // TODO error handling
    let root = root.expect("no root elem");
    match root {
        NodeDraft::XmlElement(xml_element_data, children) => init_nodes(
            &backend,
            xml_element_data,
            children,
            None,
            None,
            Arc::new(RwLock::new(())),
        ),
        NodeDraft::TextNode(_) => unreachable!(),
    }
}

fn init_nodes(
    backend: &PersistXml,
    xml_element_data: XmlElementData,
    children: Vec<NodeDraft>,
    parent: Option<Weak<dyn XmlElement>>,
    prev_sibling: Option<NodeWeak>,
    lock_for_current_level: Arc<RwLock<()>>,
) -> Arc<dyn XmlElement> {
    let node_data_inner = NodeDataInner::Init(NodeDataInit {
        parent,
        prev_sibling,
        next_sibling: None,
    });

    let node_data = NodeData {
        inner: UnsafeCell::new(node_data_inner),
        lock: UnsafeCell::new(lock_for_current_level),
        lock_swap_protection: RwLock::new(()),
    };

    let lock_for_child_level = Arc::clone(&xml_element_data.children.lock);

    let node = if let Some(init_fn) = backend.mapped_initialisers.get(&xml_element_data.tag_name) {
        init_fn(node_data, xml_element_data)
    } else {
        Arc::new(BaseXmlElement {
            node_data,
            xml_element_data,
        })
    };

    let children_len = children.len();
    let mut head: Option<Node> = None;
    let mut prev_sibling: Option<Node> = None;

    for child_draft in children {
        let child = match child_draft {
            NodeDraft::XmlElement(xml_element_data, children) => Node::XmlElement(init_nodes(
                &backend,
                xml_element_data,
                children,
                Some(Arc::downgrade(&node)),
                prev_sibling.clone().map(|prev| prev.downgrade()),
                lock_for_child_level.clone(),
            )),
            NodeDraft::TextNode(text) => {
                let node_data_inner = NodeDataInner::Init(NodeDataInit {
                    parent: Some(Arc::downgrade(&node)),
                    prev_sibling: prev_sibling.clone().map(|prev| prev.downgrade()),
                    next_sibling: None,
                });

                let text_node_data = NodeData {
                    inner: UnsafeCell::new(node_data_inner),
                    lock: UnsafeCell::new(lock_for_child_level.clone()),
                    lock_swap_protection: RwLock::new(()),
                };

                Node::Text(Arc::new(TextNode {
                    node_data: text_node_data,
                    text,
                }))
            }
        };

        if let Some(ref mut prev) = prev_sibling {
            if let Some(mut mut_prev) = prev.try_borrow_mut() {
                mut_prev
                    .get_node_data_mut()
                    .get_mut()
                    .set_next_sibling(child.clone())
            } else {
                let mut prev_node_data = prev.get_node_data().write();
                prev_node_data.set_next_sibling(child.clone());
            }
        } else {
            if head.replace(child.clone()).is_some() {
                unreachable!();
            }
        }

        prev_sibling = Some(child);
    }

    let node_list = &node.get_xml_element_data().children;
    let node_list_guard = node_list.lock.write();

    // SAFETY:
    // Mutable access to the cells is safe because the write lock has been acquired.
    unsafe {
        *node_list.head.get() = head;
        *node_list.tail.get() = prev_sibling.map(|last| last.downgrade());
    };
    node_list
        .len
        .store(children_len, std::sync::atomic::Ordering::Relaxed);
    drop(node_list_guard);

    node
}

fn create_node_draft<B: BufRead>(elem: &BytesStart, reader: &Reader<B>) -> NodeDraft {
    // TODO error handling
    let tag_name = String::from(std::str::from_utf8(elem.name()).unwrap());

    let mut attr_map = HashMap::new();
    for attr in elem.attributes() {
        // TODO error handling
        let attr = attr.unwrap();
        let attr_val = attr.unescape_and_decode_value(&reader).unwrap();
        let xml_attr = XmlAttribute { str_val: attr_val };

        attr_map.insert(String::from(from_utf8(attr.key).unwrap()), xml_attr);
    }

    let xml_element_data = XmlElementData {
        tag_name,
        children: NodeList {
            head: UnsafeCell::new(None),
            tail: UnsafeCell::new(None),
            len: std::sync::atomic::AtomicUsize::new(0),
            lock: Arc::new(RwLock::new(())),
        },
        attributes: attr_map,
    };

    NodeDraft::XmlElement(xml_element_data, Vec::new())
}

enum NodeDraft {
    TextNode(String),
    XmlElement(XmlElementData, Vec<NodeDraft>),
}

impl NodeDraft {
    fn adopt_child(&mut self, node_draft: NodeDraft) {
        match self {
            NodeDraft::XmlElement(.., children) => {
                children.push(node_draft);
            }
            // TextNodes can't have children
            NodeDraft::TextNode(..) => unreachable!(),
        }
    }
}
