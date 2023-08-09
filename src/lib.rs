mod aff;
mod dic;

pub struct Dictionary {
    _dic: dic::Dic,
    _aff: aff::Aff,
    // TODO: personal dictionaries & session changes
}

impl Dictionary {
    // TODO: Result
    pub fn compile(_aff_text: &str, _dic_text: &str) -> Self {
        unimplemented!()
    }

    pub fn check(&self, _word: &str) -> bool {
        unimplemented!()
    }

    pub fn suggest(&self, _word: &str) -> Vec<String> {
        unimplemented!()
    }
}
