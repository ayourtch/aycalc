# aycalc
A very simple embeddable calculator

This project implements a small embeddable calculator, with support for basic arithmetic operations,
ternary conditional, integer (everything is int128) + string types, and ability to read the data from supplied
variables (via a trait) and functions (via another trait).

There is a very basic example:

```
$ cargo run --example test1 "41 + test"
    Finished dev [unoptimized + debuginfo] target(s) in 0.01s
     Running `target/debug/examples/test1 '41 + test'`
Getting the variable 'test'
Got string value: 1
Conversion result to CalcVal: Ok(Int(1))
Parse result: Ok(Int(42))
```


