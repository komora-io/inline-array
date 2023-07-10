# inline-array

<a href="https://docs.rs/inline-array"><img src="https://docs.rs/inline-array/badge.svg"></a>

`InlineArray` is a stack-inlinable array of bytes that is intended for situations where many bytes
are being shared in database-like scenarios, where optimizing for space usage is extremely
important.

`InlineArray` uses 8 bytes on the stack. It will inline arrays of up to 7 bytes. If the bytes
are longer than that, it will store them in an optimized reference-count-backed structure of
two different variants. For arrays up to length 255, the data is stored with an `AtomicU8`
reference counter and `u8` length field, for only two bytes of overhead. For values larger
than that, they are stored with an `AtomicU16` reference counter and a 48-bit length field.
If the maximum counter is reached for either variant, the bytes are copied into a new
`InlineArray` with a fresh reference count of 1. This is made with the assumption that most
reference counts will be far lower than 2^16 and only rarely surpassing 255 in the small case.

The inline and both types of shared instances of `InlineArray` guarantee that the stored array is
always aligned to 8-byte boundaries, regardless of if it is inline on the stack or
shared on the heap. This is advantageous for using in combination with certain
zero-copy serialization techniques that require alignment guarantees.

Byte arrays that require more than 48 bits to store their length (256 terabytes) are not supported.

`InlineArray::make_mut` can be used for getting a mutable reference to the bytes in this
structure. If the shared reference counter is higher than  1, this acts like a `Cow` and
will make self into a private copy that is safe for modification.

# Features

* `serde` implements `serde::Serialize` and `serde::Deserialize` for `InlineArray` (disabled by
default)

# Examples

```rust
use inline_array::InlineArray;

let ia = InlineArray::from(b"yo!");

// then use it more or less like you would an Arc<[u8]>
```

