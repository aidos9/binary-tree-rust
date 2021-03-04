use std::cell::RefCell;
use std::rc::Rc;

pub type WrappedNode<T> = Rc<RefCell<Node<T>>>;

#[derive(Clone)]
pub struct Node<T: Clone + PartialOrd + PartialEq> {
    value: Option<T>,
    left: Option<WrappedNode<T>>,
    right: Option<WrappedNode<T>>,
}

impl<T> Node<T>
where
    T: Clone + PartialOrd + PartialEq,
{
    pub fn new(value: T) -> Self {
        return Self {
            value: Some(value),
            left: None,
            right: None,
        };
    }

    pub fn matches_left(&self, value: &T) -> bool {
        if let Some(left) = self.left().as_ref() {
            return left.borrow().value() == value;
        } else {
            return false;
        }
    }

    pub fn set_value(&mut self, value: T) {
        self.value = Some(value);
    }

    pub fn set_left(&mut self, node: Node<T>) {
        self.left = Some(crate::new_wrapped_node!(node));
    }

    pub fn set_left_ptr(&mut self, node: WrappedNode<T>) {
        self.left = Some(node);
    }

    pub fn set_right(&mut self, node: Node<T>) {
        self.right = Some(crate::new_wrapped_node!(node));
    }

    pub fn set_right_ptr(&mut self, ptr: WrappedNode<T>) {
        self.right = Some(ptr);
    }

    pub fn set_right_none(&mut self) {
        self.right = None;
    }

    pub fn set_left_none(&mut self) {
        self.left = None;
    }

    pub fn has_right(&self) -> bool {
        return self.right.is_some();
    }

    pub fn has_left(&self) -> bool {
        return self.left.is_some();
    }

    pub fn value(&self) -> &T {
        return self.value.as_ref().unwrap();
    }

    pub fn take_value(&mut self) -> T {
        return self.value.take().unwrap();
    }

    pub fn left(&self) -> Option<WrappedNode<T>> {
        return self.left.clone();
    }

    pub fn right(&self) -> Option<WrappedNode<T>> {
        return self.right.clone();
    }
}
