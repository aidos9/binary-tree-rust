mod binary_tree_set;
mod node;

pub use binary_tree_set::BinaryTreeSet;

#[macro_export]
macro_rules! new_wrapped_node {
    ($node:expr) => {
        std::rc::Rc::new(std::cell::RefCell::new($node));
    };
}
