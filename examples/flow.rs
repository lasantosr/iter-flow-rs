#![allow(dead_code)]

use anyhow::{bail, Error, Result};
use iter_flow::Iterflow;

fn main() -> Result<()> {
    let res = (0..4)
        .map(|n| if n == 0 { Err("invalid!") } else { Ok(n - 1) })
        .and_then(|n| if n > 0 { Ok(n - 1) } else { Err("illegal!") })
        .map_ok(|n| (n + 1) * 2)
        .flat_map_ok(|n| (0..n));

    for r in res {
        println!("{r:?}")
    }

    Ok(())
}

fn get_ids() -> Result<impl Iterator<Item = u32>> {
    Ok(0..5)
}

fn find_foo(id: u32) -> Result<Foo> {
    if id == 0 {
        bail!("Not Found")
    }

    Ok(Foo { id, bar: id - 1 })
}

fn subtract_1(n: u32) -> Result<u32> {
    if n < 1 {
        bail!("illegal operation")
    }
    Ok(n - 1)
}

fn to_range(n: u32) -> impl Iterator<Item = u32> {
    0..=n
}

fn add_err_context(ctx: &'static str) -> impl Fn(Error) -> Error {
    move |err: Error| err.context(ctx)
}

struct Foo {
    id: u32,
    bar: u32,
}

impl Foo {
    fn bar(&self) -> u32 {
        self.bar
    }
}

/*
!! Iterator can be IntoIter

Result<T, E>:
    - map( T -> X )                                             | Result<X, E>
    - and_then( T -> Result<X, Into<E>> )                       | Result<X, E>

Once mapped to Result<Iter>, `?` can be used and we're back on an Iterator

Iterator<T>:
    - map( T -> X )                                             | Iterator<X>

Once we've got Iterator<Result>, flow begins


Iterator<Result<T, E>>:
    - map_err( E -> Z )                                         | Iterator<Result<T, Z>>
    - map_ok( T -> X )                                          | Iterator<Result<X, Z>>
    - and_then( T -> Result<X, Into<E>> )                       | Iterator<Result<X, E>>
    - flat_map_ok( T -> Iterator<X> )                           | Iterator<Result<X, E>>
    - and_then_flat( T -> Result<Iterator<X>, Into<E>> )        | Iterator<Result<X, E>>
    - finish()                                                  | Result<Iterator<X>, E>

+ await

!! Use Borrow when reference, so it can be both reference and regular


*/
