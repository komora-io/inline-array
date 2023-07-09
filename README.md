# inline-array

<a href="https://docs.rs/inline-array"><img src="https://docs.rs/inline-array/badge.svg"></a>

`InlineArray` is a stack-inlinable array of bytes that is intended for situations where many bytes
are being shared in database-like scenarios, where optimizing for space usage is extremely
important.

`InlineArray` uses 8 bytes on the stack. It will inline arrays of up to 7 bytes. If the bytes
are longer than that, it will store them in an optimized reference-count-backed structure,
where the atomic reference count is 16 bytes. If the maximum counter is reached, the bytes
are copied into a new `InlineArray` with a fresh reference count of 1. This is made with
the assumption that most reference counts will be far lower than 2^16.

Both the inline and shared instances of `InlineArray` guarantee that the stored array is
always aligned to 8-byte boundaries, regardless of if it is inline on the stack or
shared on the heap. This is advantageous for using in combination with certain
zero-copy serialization techniques.

The 16-bit reference counter is stored packed with a 48-bit length field at the beginning
of the shared array. Byte arrays that require more than 48 bits to store their length
(256 terabytes) are not supported.

`InlineArray::make_mut` can be used for getting a mutable reference to the bytes in this
structure. If the shared reference counter is higher than  1, this acts like a `Cow` and
will make self into a private copy that is safe for modification.
