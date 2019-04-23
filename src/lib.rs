pub mod map;
pub mod set;

pub use self::{map::OrdMap, set::OrdSet};

/// Create an `OrdMap` from a list of key-value pairs
///
/// ## Example
///
/// ```
/// #[macro_use] extern crate ordmap;
/// # fn main() {
///
/// let map = ordmap!{
///     "a" => 1,
///     "b" => 2,
/// };
/// assert_eq!(map["a"], 1);
/// assert_eq!(map["b"], 2);
/// assert_eq!(map.get("c"), None);
///
/// // "a" is the first key
/// assert_eq!(map.keys().next(), Some(&"a"));
/// # }
/// ```
#[macro_export]
macro_rules! ordmap {
    (__SINGLE $($x:tt)*) => (());
    (__COUNT $($rest:expr),*) => (<[()]>::len(&[$(ordmap!(__SINGLE $rest)),*]));

    ($($key:expr => $value:expr,)+) => { ordmap!($($key => $value),+) };
    ($($key:expr => $value:expr),*) => {
        {
            let _cap = ordmap!(__COUNT $($key),*);
            let mut _map = $crate::OrdMap::with_capacity(_cap);
            $(
                _map.insert($key, $value);
            )*
            _map
        }
    };

    (@str $($key:expr => $value:expr,)+) => { ordmap!(@str $($key => $value),+) };
    (@str $($key:expr => $value:expr),*) => {
        {
            let _cap = ordmap!(__COUNT $($key),*);
            let mut _map = $crate::OrdMap::with_capacity(_cap);
            $(
                _map.insert($key.to_string(), $value);
            )*
            _map
        }
    }
}

/// Create an `OrdSet` from a list of values
///
/// ## Example
///
/// ```
/// #[macro_use] extern crate ordmap;
/// # fn main() {
///
/// let set = ordset!{
///     "a",
///     "b",
/// };
/// assert!(set.contains("a"));
/// assert!(set.contains("b"));
/// assert!(!set.contains("c"));
///
/// // "a" is the first value
/// assert_eq!(set.iter().next(), Some(&"a"));
/// # }
/// ```
#[macro_export]
macro_rules! ordset {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(ordset!(@single $rest)),*]));

    ($($value:expr,)+) => { ordset!($($value),+) };
    ($($value:expr),*) => {
        {
            let _cap = ordset!(@count $($value),*);
            let mut _set = $crate::OrdSet::with_capacity(_cap);
            $(
                _set.insert($value);
            )*
            _set
        }
    };
}
