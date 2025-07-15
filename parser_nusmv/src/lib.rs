pub mod parser_nusmv; // or whatever your module file is

pub use parser_nusmv::parse_smv; // <- this line makes `parse_model` accessible from the root