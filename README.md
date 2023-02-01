# Iterflow

Functional programming utilities for Rust.

This crate is heavily inspired by [itertools](https://crates.io/crates/itertools) but with the main focus of chaining 
operations to develop in a declarative approach (as opposed to usual imperative)


```rust
fn sub_1(n: u32) -> Result<u32, &'static str> {
    if n == 0 { Err("illegal!") } else { Ok(n - 1) }
}

fn math_calc(n: u32) -> u32 {
    (n + 1) * 2
}

fn to_range(n: u32) -> Range<u32> {
    0..n
}

let it = (0..4)
    .map(sub_1)
    .and_then(sub_1)
    .map_ok(math_calc)
    .flat_map_ok(to_range);

iter_flow::assert_equal(
    it,
    vec![
        Err("illegal!"),
        Err("illegal!"),
        Ok(0),
        Ok(1),
        Ok(0),
        Ok(1),
        Ok(2),
        Ok(3),
    ],
);
```

TODO:
- [ ] Support for async/await with Futures

## License

Iterflow is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for the full license text.