# approx_collections

Collections using approximate floating-point comparison.

See [the docs](https://docs.rs/approx_collections/latest/approx_collections/) for a list of collections and crate features.

## Testing

I recommend setting the environment variable `PROPTEST_CASES` to `1_000_000` to test more cases (default is only `256`) and running tests using `cargo test --release`.
