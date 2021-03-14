use std::{path::PathBuf, sync::Arc};

use quick_xml::{Error, Reader};

use crate::{serialiser, PersistXml, XmlElement};

pub struct Context {
    backing_file: Option<PathBuf>,
    root_element: Arc<dyn XmlElement>,
}

impl Context {
    pub fn create_for_file(backend: &PersistXml, path: PathBuf) -> Result<Self, Error> {
        let reader = Reader::from_file(path.clone())?;
        let root_element = serialiser::parse_tree(reader, backend);

        Ok(Context {
            backing_file: Some(path),
            root_element,
        })
    }

    pub fn create_for_str(backend: &PersistXml, xml_str: &str) -> Self {
        let reader = Reader::from_str(xml_str);
        let root_element = serialiser::parse_tree(reader, backend);

        Context {
            backing_file: None,
            root_element,
        }
    }

    pub fn root_element(&self) -> Arc<dyn XmlElement> {
        self.root_element.clone()
    }
}
