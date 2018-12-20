use std::num::Wrapping;

fn mix(a: &mut Wrapping<u32>, b: &mut Wrapping<u32>, c: &mut Wrapping<u32>) {
    *a -= *b; *a -= *c; *a ^= *c >> 13;
    *b -= *c; *b -= *a; *b ^= *a << 8;
    *c -= *a; *c -= *b; *c ^= *b >> 13;
    *a -= *b; *a -= *c; *a ^= *c >> 12;
    *b -= *c; *b -= *a; *b ^= *a << 16;
    *c -= *a; *c -= *b; *c ^= *b >> 5;
    *a -= *b; *a -= *c; *a ^= *c >> 3;
    *b -= *c; *b -= *a; *b ^= *a << 10;
    *c -= *a; *c -= *b; *c ^= *b >> 15;
}

pub fn hash<T: Copy + Into<u32>>(arr: &[T]) -> u32 {
    hash_with(arr, |u| Wrapping((*u).into()), Wrapping(31))
}

pub fn hash_with<T, H: Fn(&T) -> Wrapping<u32>>(arr: &[T], h: H, init_value: Wrapping<u32>) -> u32 {
    let mut a: Wrapping<u32> = Wrapping(0x9e3779b9);
    let mut b = a;
    let mut c: Wrapping<u32> = Wrapping(11);
    let mut n = arr.len();
    match n {
        1 => {
            a += init_value;
            b = h(&arr[0]);
            mix(&mut a, &mut b, &mut c); c.0 },
        2 => {
            a += init_value;
            b += h(&arr[0]);
            c += h(&arr[1]);
            mix(&mut a, &mut b, &mut c); c.0 },
        3 => {
            a += h(&arr[0]);
            b += h(&arr[1]);
            c += h(&arr[2]);
            mix(&mut a, &mut b, &mut c);
            a += init_value;
            mix(&mut a, &mut b, &mut c); c.0 },
        _ => {
            while n >= 3 {
                n -= 1; a += h(&arr[n]);
                n -= 1; b += h(&arr[n]);
                n -= 1; c += h(&arr[n]);
                mix(&mut a, &mut b, &mut c);
            }
            a += init_value;
            match n {
                2 => { b += h(&arr[1]); c += h(&arr[0]); },
                1 => c += h(&arr[0]),
                _ => ()
            };
            mix(&mut a, &mut b, &mut c); c.0 }
    }
}
