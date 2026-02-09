//! `expect(unused)` should not trigger an `unfulfilled_lint_expectation` on an implemented but
//! unused trait.
//!
//! Regression test for https://github.com/rust-lang/rust/issues/152370.
//@ compile-flags: -Wunused
//@ check-pass
#[expect(unused)]
trait UnusedTrait {}

struct UsedStruct(u32);

impl UnusedTrait for UsedStruct {}

fn main() {
    let x = UsedStruct(12);
    println!("Hello world! {}", x.0);
}
