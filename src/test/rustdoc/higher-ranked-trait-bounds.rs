#![crate_name = "foo"]

// @has foo/trait.Trait.html
pub trait Trait<'x> {}

// @has foo/fn.test1.html
// @has - '//pre' "pub fn test1<T>() where for<'a> &'a T: Iterator,"
pub fn test1<T>()
where
    for<'a> &'a T: Iterator,
{
}

// @has foo/fn.test2.html
// @has - '//pre' "pub fn test2<T>() where for<'a, 'b> &'a T: Trait<'b>,"
pub fn test2<T>()
where
    for<'a, 'b> &'a T: Trait<'b>,
{
}

// @has foo/fn.test3.html
// @has - '//pre' "pub fn test3<F>() where F: for<'a, 'b> Fn(&'a u8, &'b u8),"
pub fn test3<F>()
where
    F: for<'a, 'b> Fn(&'a u8, &'b u8),
{
}

// @has foo/struct.Foo.html
pub struct Foo<'a> {
    _x: &'a u8,
    pub some_trait: &'a dyn for<'b> Trait<'b>,
    pub some_func: for<'c> fn(val: &'c i32) -> i32,
}

// @has - '//span[@id="structfield.some_func"]' "some_func: for<'c> fn(val: &'c i32) -> i32"
// @has - '//span[@id="structfield.some_trait"]' "some_trait: &'a dyn for<'b> Trait<'b>"

impl<'a> Foo<'a> {
    // @has - '//code' "pub fn bar<T>() where T: Trait<'a>,"
    pub fn bar<T>()
    where
        T: Trait<'a>,
    {
    }
}

// @has foo/trait.B.html
pub trait B<'x> {}

// @has - '//code[@class="in-band"]' "impl<'a> B<'a> for dyn for<'b> Trait<'b>"
impl<'a> B<'a> for dyn for<'b> Trait<'b> {}
