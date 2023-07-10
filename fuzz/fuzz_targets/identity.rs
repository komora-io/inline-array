#![no_main]
use libfuzzer_sys::fuzz_target;

use inline_array::InlineArray;

fn prop_identity(inline_array: &InlineArray) -> bool {
    let mut iv2 = inline_array.clone();

    if iv2 != inline_array {
        println!("expected clone to equal original");
        return false;
    }

    if *inline_array != *iv2 {
        println!("expected AsMut to equal original");
        return false;
    }

    if &*inline_array != iv2.make_mut() {
        println!("expected AsMut to equal original");
        return false;
    }

    let buf: &[u8] = inline_array.as_ref();
    assert_eq!(buf.as_ptr() as usize % 8, 0);

    let ptr = iv2.into_raw();
    let rt = unsafe { InlineArray::from_raw(ptr) };
    assert_eq!(&rt, inline_array);

    if inline_array.is_empty() {
        assert_eq!(inline_array, &inline_array::EMPTY);
    }

    true
}

fuzz_target!(|data: &[u8]| {
    let ia = InlineArray::from(data);
    prop_identity(&ia);
});
