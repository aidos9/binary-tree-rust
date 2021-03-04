use crate::node::{Node, WrappedNode};

#[derive(Clone)]
pub struct BinaryTreeSet<T: Clone + PartialOrd + PartialEq> {
    root_node: Option<WrappedNode<T>>,
}

impl<T> BinaryTreeSet<T>
where
    T: Clone + PartialOrd + PartialEq,
{
    pub fn new() -> Self {
        return Self { root_node: None };
    }

    pub fn is_empty(&self) -> bool {
        return self.root_node.is_none();
    }

    pub fn min(&self) -> Option<T> {
        let mut current = self.root_node.clone()?;

        loop {
            let nxt = if let Some(nxt) = current.borrow().left() {
                nxt
            } else {
                break;
            };

            current = nxt;
        }

        return Some(current.borrow().value().clone());
    }

    pub fn max(&self) -> Option<T> {
        let mut current = self.root_node.clone()?;

        loop {
            let nxt = if let Some(nxt) = current.borrow().right() {
                nxt
            } else {
                break;
            };

            current = nxt;
        }

        return Some(current.borrow().value().clone());
    }

    pub fn insert(&mut self, value: T) {
        if self.root_node.is_none() {
            self.root_node = Some(crate::new_wrapped_node!(Node::new(value)));
            return;
        }

        let mut parent = self.root_node.clone().unwrap();

        loop {
            if &value < parent.borrow().value() {
                if parent.borrow().left().is_none() {
                    parent.borrow_mut().set_left(Node::new(value));
                    break;
                } else {
                    let next_parent = parent.borrow_mut().left().unwrap();
                    parent = next_parent;
                }
            } else if &value > parent.borrow().value() {
                if parent.borrow().right().is_none() {
                    parent.borrow_mut().set_right(Node::new(value));
                    break;
                } else {
                    let next_parent = parent.borrow().right().unwrap();
                    parent = next_parent;
                }
            } else {
                return;
            }
        }
    }

    pub fn remove(&mut self, value: &T) {
        if self.root_node.is_none() {
            return;
        }

        if self.root_node.as_ref().unwrap().borrow().value() == value {
            let next = self.root_node.as_ref().unwrap().borrow().right();
            self.root_node = next;
            return;
        }

        if let Some((parent, node)) = self.find_node_with_value(value) {
            let parent = parent.unwrap();

            if node.borrow_mut().has_left() {
                let max = self.take_max(Some(node.clone()), node.borrow().left().unwrap());
                node.borrow_mut().set_value(max);
            } else {
                if node.borrow_mut().has_right() {
                    if parent.borrow().matches_left(value) {
                        parent
                            .borrow_mut()
                            .set_left_ptr(node.borrow().right().unwrap());
                    } else {
                        parent
                            .borrow_mut()
                            .set_right_ptr(node.borrow().right().unwrap());
                    }
                } else {
                    if parent.borrow().matches_left(value) {
                        parent.borrow_mut().set_left_none();
                    } else {
                        parent.borrow_mut().set_right_none();
                    }
                }
            }
        }
    }

    fn take_max(&mut self, mut parent: Option<WrappedNode<T>>, mut current: WrappedNode<T>) -> T {
        while current.borrow().has_right() {
            parent = Some(current);
            current = parent.as_ref().unwrap().borrow().right().unwrap();
        }

        if parent.is_some() {
            parent.unwrap().borrow_mut().set_right_none();
        } else {
            self.root_node = None;
        }

        return current.borrow_mut().take_value();
    }

    fn find_node_with_value(&self, value: &T) -> Option<(Option<WrappedNode<T>>, WrappedNode<T>)> {
        if self.root_node.is_none() {
            return None;
        }

        let mut parent = None;
        let mut outer_current = self.root_node.clone();

        while let Some(current) = outer_current {
            if value < current.borrow().value() {
                outer_current = current.borrow().left();
                parent = Some(current);
            } else if value > current.borrow().value() {
                outer_current = current.borrow().right();
                parent = Some(current);
            } else {
                return Some((parent, current));
            }
        }

        return None;
    }

    pub fn contains(&self, value: &T) -> bool {
        if self.root_node.is_none() {
            return false;
        }

        let mut outer_current = self.root_node.clone();

        while let Some(current) = outer_current {
            if value < current.borrow().value() {
                outer_current = current.borrow().left();
            } else if value > current.borrow().value() {
                outer_current = current.borrow().right();
            } else {
                return true;
            }
        }

        return false;
    }

    pub fn stack_into_pre_order_stack(self) -> Vec<T> {
        let mut res = Vec::new();

        if self.root_node.is_none() {
            return res;
        }

        let mut working_stack = Vec::new();

        working_stack.push(self.root_node.unwrap());

        while !working_stack.is_empty() {
            let next = working_stack.pop().unwrap();
            let mut next_borrow = next.borrow_mut();
            let (left, right, value) = (
                next_borrow.left(),
                next_borrow.right(),
                next_borrow.take_value(),
            );

            res.push(value);

            if let Some(right) = right {
                working_stack.push(right);
            }

            if let Some(left) = left {
                working_stack.push(left);
            }
        }

        return res;
    }

    pub fn stack_into_in_order_stack(self) -> Vec<T> {
        let mut res = Vec::new();

        let mut current = self.root_node.clone();

        loop {
            if current.is_none() {
                break;
            }

            let node = current.unwrap();

            if node.borrow().left().is_some() {
                let mut prev = node.borrow().left().unwrap();

                loop {
                    if prev.borrow().right().is_some()
                        && prev.borrow().right().unwrap().borrow().value() != node.borrow().value()
                    {
                        let next_prev = prev.borrow().right().unwrap();
                        prev = next_prev;
                    } else {
                        break;
                    }
                }

                if prev.borrow().right().is_some() {
                    prev.borrow_mut().set_right_none();
                    res.push(node.borrow_mut().take_value());
                    current = node.borrow().right();
                } else {
                    prev.borrow_mut().set_right_ptr(node.clone());
                    current = node.borrow().left();
                }
            } else {
                let node = node.borrow_mut();
                res.push(node.value().clone());
                current = node.right();
            };
        }

        return res;
    }

    pub fn pre_order_stack(&self) -> Vec<T> {
        fn recursive_call<T: Clone + PartialOrd + PartialEq>(
            stack: &mut Vec<T>,
            node: &WrappedNode<T>,
        ) {
            stack.push(node.borrow().value().clone());

            if let Some(node) = node.borrow().left().as_ref() {
                recursive_call(stack, node);
            }

            if let Some(node) = node.borrow().right().as_ref() {
                recursive_call(stack, node);
            }
        }

        let mut stack = Vec::new();

        if let Some(node) = self.root_node.as_ref() {
            recursive_call(&mut stack, node);
        }

        return stack;
    }

    pub fn in_order_stack(&self) -> Vec<T> {
        fn recursive_call<T: Clone + PartialOrd + PartialEq>(
            stack: &mut Vec<T>,
            node: &WrappedNode<T>,
        ) {
            if let Some(node) = node.borrow().left().as_ref() {
                recursive_call(stack, node);
            }

            stack.push(node.borrow().value().clone());

            if let Some(node) = node.borrow().right().as_ref() {
                recursive_call(stack, node);
            }
        }

        let mut stack = Vec::new();

        if let Some(node) = self.root_node.as_ref() {
            recursive_call(&mut stack, node);
        }

        return stack;
    }

    pub fn into_in_order_stack(self) -> Vec<T> {
        fn recursive_call<T: Clone + PartialOrd + PartialEq>(
            stack: &mut Vec<T>,
            node: &WrappedNode<T>,
        ) {
            if let Some(node) = node.borrow().left().as_ref() {
                recursive_call(stack, node);
            }

            stack.push(node.borrow_mut().take_value());

            if let Some(node) = node.borrow().right().as_ref() {
                recursive_call(stack, node);
            }
        }

        let mut stack = Vec::new();

        if let Some(node) = self.root_node.as_ref() {
            recursive_call(&mut stack, node);
        }

        return stack;
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for BinaryTreeSet<T>
where
    T: Clone + PartialOrd + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(f, "{:?}", self.in_order_stack());
    }
}

impl<T> IntoIterator for BinaryTreeSet<T>
where
    T: Clone + PartialOrd + PartialEq,
{
    type Item = T;

    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        return self.into_in_order_stack().into_iter();
    }
}

#[cfg(test)]
mod tests {
    use super::{BinaryTreeSet, Node};

    mod min_tests {
        use super::*;

        #[test]
        fn test_min_1() {
            let tree = BinaryTreeSet::<usize>::new();
            assert_eq!(tree.min(), None);
        }

        #[test]
        fn test_min_2() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.root_node = Some(crate::new_wrapped_node!(Node::new(22)));
            assert_eq!(tree.min(), Some(22));
        }

        #[test]
        fn test_min_3() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.insert(22);
            tree.insert(12);

            assert_eq!(tree.min(), Some(12));
        }
    }

    mod max_tests {
        use super::*;

        #[test]
        fn test_max_1() {
            let tree = BinaryTreeSet::<usize>::new();
            assert_eq!(tree.max(), None);
        }

        #[test]
        fn test_max_2() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.insert(22);
            assert_eq!(tree.max(), Some(22));
        }

        #[test]
        fn test_max_3() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.insert(22);
            tree.insert(12);

            assert_eq!(tree.max(), Some(22));
        }

        #[test]
        fn test_max_4() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.insert(22);
            tree.insert(23);

            assert_eq!(tree.max(), Some(23));
        }
    }

    mod insert_tests {
        use super::*;

        #[test]
        fn test_insert_1() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert_eq!(*tree.root_node.unwrap().borrow().value(), 23);
        }

        #[test]
        fn test_insert_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);

            assert_eq!(
                *tree
                    .root_node
                    .unwrap()
                    .borrow()
                    .left()
                    .unwrap()
                    .borrow()
                    .value(),
                12
            );
        }

        #[test]
        fn test_insert_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);
            tree.insert(16);

            assert_eq!(
                *tree
                    .root_node
                    .unwrap()
                    .borrow()
                    .left()
                    .unwrap()
                    .borrow()
                    .right()
                    .unwrap()
                    .borrow()
                    .value(),
                16
            );
        }

        #[test]
        fn test_insert_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);
            tree.insert(16);
            tree.insert(25);
            tree.insert(26);

            assert_eq!(
                *tree
                    .root_node
                    .unwrap()
                    .borrow()
                    .right()
                    .unwrap()
                    .borrow()
                    .right()
                    .unwrap()
                    .borrow()
                    .value(),
                26
            );
        }
    }

    mod contains_tests {
        use super::*;

        #[test]
        fn test_contains_1() {
            let tree = BinaryTreeSet::<usize>::new();

            assert!(!tree.contains(&26));
        }

        #[test]
        fn test_contains_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);
            tree.insert(16);
            tree.insert(25);
            tree.insert(26);

            assert!(tree.contains(&26));
        }

        #[test]
        fn test_contains_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);
            tree.insert(16);
            tree.insert(25);
            tree.insert(26);

            assert!(!tree.contains(&28));
        }

        #[test]
        fn test_contains_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);
            tree.insert(16);
            tree.insert(25);
            tree.insert(26);

            assert!(tree.contains(&12));
        }

        #[test]
        fn test_contains_5() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(12);
            tree.insert(16);
            tree.insert(25);
            tree.insert(26);

            assert!(!tree.contains(&0));
        }

        #[test]
        fn test_contains_6() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert!(tree.contains(&23));
        }
    }

    mod iterative_tests {
        use super::*;

        #[test]
        fn test_stack_pre_order_stack_1() {
            let tree = BinaryTreeSet::<usize>::new();

            assert_eq!(tree.stack_into_pre_order_stack(), Vec::new());
        }

        #[test]
        fn test_stack_pre_order_stack_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert_eq!(tree.stack_into_pre_order_stack(), vec![23]);
        }

        #[test]
        fn test_stack_pre_order_stack_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);

            assert_eq!(tree.stack_into_pre_order_stack(), vec![23, 1, 26]);
        }

        #[test]
        fn test_stack_pre_order_stack_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);
            tree.insert(28);
            tree.insert(2);

            assert_eq!(tree.stack_into_pre_order_stack(), vec![23, 1, 2, 26, 28]);
        }

        #[test]
        fn test_stack_in_order_stack_1() {
            let tree = BinaryTreeSet::<usize>::new();

            assert_eq!(tree.stack_into_in_order_stack(), Vec::new());
        }

        #[test]
        fn test_stack_in_order_stack_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert_eq!(tree.stack_into_in_order_stack(), vec![23]);
        }

        #[test]
        fn test_istack_n_order_stack_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);

            assert_eq!(tree.stack_into_in_order_stack(), vec![1, 23, 26]);
        }

        #[test]
        fn test_stack_in_order_stack_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);
            tree.insert(28);
            tree.insert(2);

            assert_eq!(tree.stack_into_in_order_stack(), vec![1, 2, 23, 26, 28]);
        }

        #[test]
        fn test_stack_in_order_stack_5() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();

            for i in 0..150 {
                tree.insert(i);
                comp.push(i);
            }

            assert_eq!(tree.stack_into_in_order_stack(), comp);
        }
    }

    mod recursive_tests {
        use super::*;

        #[test]
        fn test_into_pre_order_stack_1() {
            let tree = BinaryTreeSet::<usize>::new();

            assert_eq!(tree.pre_order_stack(), Vec::new());
        }

        #[test]
        fn test_pre_order_stack_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert_eq!(tree.pre_order_stack(), vec![23]);
        }

        #[test]
        fn test_pre_order_stack_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);

            assert_eq!(tree.pre_order_stack(), vec![23, 1, 26]);
        }

        #[test]
        fn test_pre_order_stack_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);
            tree.insert(28);
            tree.insert(2);

            assert_eq!(tree.pre_order_stack(), vec![23, 1, 2, 26, 28]);
        }

        #[test]
        fn test_in_order_stack_1() {
            let tree = BinaryTreeSet::<usize>::new();

            assert_eq!(tree.in_order_stack(), Vec::new());
        }

        #[test]
        fn test_in_order_stack_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert_eq!(tree.in_order_stack(), vec![23]);
        }

        #[test]
        fn test_in_order_stack_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);

            assert_eq!(tree.in_order_stack(), vec![1, 23, 26]);
        }

        #[test]
        fn test_in_order_stack_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);
            tree.insert(28);
            tree.insert(2);

            assert_eq!(tree.in_order_stack(), vec![1, 2, 23, 26, 28]);
        }

        #[test]
        fn test_in_order_stack_5() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();

            for i in 0..150 {
                tree.insert(i);
                comp.push(i);
            }

            assert_eq!(tree.in_order_stack(), comp);
        }

        #[test]
        fn test_in_order_stack_6() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();

            for i in 0..2_500 {
                tree.insert(i);
                comp.push(i);
            }

            assert_eq!(tree.in_order_stack(), comp);
        }

        #[test]
        fn test_into_in_order_stack_1() {
            let tree = BinaryTreeSet::<usize>::new();

            assert_eq!(tree.into_in_order_stack(), Vec::new());
        }

        #[test]
        fn test_into_in_order_stack_2() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);

            assert_eq!(tree.into_in_order_stack(), vec![23]);
        }

        #[test]
        fn test_into_in_order_stack_3() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);

            assert_eq!(tree.into_in_order_stack(), vec![1, 23, 26]);
        }

        #[test]
        fn test_into_in_order_stack_4() {
            let mut tree = BinaryTreeSet::<usize>::new();

            tree.insert(23);
            tree.insert(1);
            tree.insert(26);
            tree.insert(28);
            tree.insert(2);

            assert_eq!(tree.into_in_order_stack(), vec![1, 2, 23, 26, 28]);
        }

        #[test]
        fn test_into_in_order_stack_5() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();

            for i in 0..150 {
                tree.insert(i);
                comp.push(i);
            }

            assert_eq!(tree.into_in_order_stack(), comp);
        }

        #[test]
        fn test_into_in_order_stack_6() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();

            for i in 0..2_500 {
                tree.insert(i);
                comp.push(i);
            }

            assert_eq!(tree.into_in_order_stack(), comp);
        }
    }

    mod iterator_tests {
        use crate::BinaryTreeSet;

        #[test]
        fn test_iterator() {
            let mut tree = BinaryTreeSet::<usize>::new();

            for i in 0..250 {
                tree.insert(i);
            }

            for (i, val) in tree.into_iter().enumerate() {
                assert_eq!(i, val);
            }
        }
    }

    mod test_remove {
        use crate::BinaryTreeSet;

        #[test]
        fn test_remove_1() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.remove(&1);

            assert!(tree.is_empty());
        }

        #[test]
        fn test_remove_2() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.insert(1);
            tree.remove(&1);

            assert!(tree.is_empty());
        }

        #[test]
        fn test_remove_3() {
            let mut tree = BinaryTreeSet::<usize>::new();
            tree.insert(1);
            tree.insert(12);
            tree.insert(33);
            tree.insert(2);
            tree.remove(&1);

            assert_eq!(tree.into_in_order_stack(), vec![2, 12, 33]);
        }

        #[test]
        fn test_remove_4() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();
            for i in 0..15 {
                tree.insert(i);

                if i != 12 {
                    comp.push(i);
                }
            }

            tree.remove(&12);

            assert_eq!(tree.into_in_order_stack(), comp);
        }

        #[test]
        fn test_remove_5() {
            let mut tree = BinaryTreeSet::<usize>::new();
            let mut comp = Vec::new();

            for i in 0..=75 {
                tree.insert(75 + i);
                tree.insert(75 - i);
            }

            for i in 0..=150 {
                if i != 122 {
                    comp.push(i);
                }
            }

            tree.remove(&122);

            assert_eq!(tree.into_in_order_stack(), comp);
        }
    }
    #[test]
    fn test_creation() {
        assert!(BinaryTreeSet::<usize>::new().is_empty());
    }
}
