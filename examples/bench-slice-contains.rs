//! A benchmark for the different possible strategies of looking up a flag in a flagset.
//!
//! Originally I thought that binary search in a sorted flagset would clearly be better but it's
//! actually typically 1-2ns worse (24ns total) for these cases. Flagsets are probably always
//! small enough that binary search adds more overhead than it's worth.
//!
//! TODO: measure a histogram of flagset lengths in real `.dic` files. If binary search is causing
//! more harm than good, let's switch `FlagSet::contains` to use `slice::contains`. Maybe drop the
//! FlagSet wrapper struct completely and just use `Box<[Flag]>`.

use brunch::Bench;
use std::hint::black_box;

type Flag = std::num::NonZeroU16;

const fn flag(ch: char) -> Flag {
    assert!(ch as u32 != 0);

    unsafe { Flag::new_unchecked(ch as u16) }
}

// en_US.dic `advise/LDRSZGB`
const MANY_FLAGS_UNSORTED: &[Flag] = &[
    flag('L'),
    flag('D'),
    flag('R'),
    flag('S'),
    flag('Z'),
    flag('G'),
    flag('B'),
];
const MANY_FLAGS_SORTED: &[Flag] = &[
    flag('B'),
    flag('D'),
    flag('G'),
    flag('L'),
    flag('R'),
    flag('S'),
    flag('Z'),
];

// en_US.dic `advent/SM`
const FEW_FLAGS_UNSORTED: &[Flag] = &[flag('S'), flag('M')];
const FEW_FLAGS_SORTED: &[Flag] = &[flag('M'), flag('S')];

const EMPTY_FLAGS: &[Flag] = &[];

const UNKNOWN_FLAG_HIGH: Flag = flag('Z');
const UNKNOWN_FLAG_LOW: Flag = flag('A');

const D_FLAG: Flag = flag('D');

const SAMPLES: u32 = 5_000_000;

brunch::benches!(
    Bench::new("contains: lookup non-existing high in many flags unsorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_UNSORTED).contains(black_box(&UNKNOWN_FLAG_HIGH))),
    Bench::new("contains: lookup non-existing high in many flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_SORTED).contains(black_box(&UNKNOWN_FLAG_HIGH))),
    Bench::new("contains: lookup non-existing low in many flags unsorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_UNSORTED).contains(black_box(&UNKNOWN_FLAG_LOW))),
    Bench::new("contains: lookup non-existing low in many flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_SORTED).contains(black_box(&UNKNOWN_FLAG_LOW))),
    Bench::new("contains: lookup 'D' in many flags unsorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_UNSORTED).contains(black_box(&D_FLAG))),
    Bench::new("contains: lookup 'D' in many flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_SORTED).contains(black_box(&D_FLAG))),
    // ---
    Bench::new("contains: lookup non-existing high in few flags unsorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_UNSORTED).contains(&UNKNOWN_FLAG_HIGH)),
    Bench::new("contains: lookup non-existing high in few flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_SORTED).contains(&UNKNOWN_FLAG_HIGH)),
    Bench::new("contains: lookup non-existing low in few flags unsorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_UNSORTED).contains(&UNKNOWN_FLAG_LOW)),
    Bench::new("contains: lookup non-existing low in few flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_SORTED).contains(&UNKNOWN_FLAG_LOW)),
    Bench::new("contains: lookup 'D' in few flags unsorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_UNSORTED).contains(black_box(&D_FLAG))),
    Bench::new("contains: lookup 'D' in few flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_SORTED).contains(black_box(&D_FLAG))),
    // ---
    Bench::new("contains: lookup non-existing high in empty flags")
        .with_samples(SAMPLES)
        .run(|| black_box(EMPTY_FLAGS).contains(&UNKNOWN_FLAG_HIGH)),
    Bench::new("contains: lookup non-existing low in empty flags")
        .with_samples(SAMPLES)
        .run(|| black_box(EMPTY_FLAGS).contains(&UNKNOWN_FLAG_LOW)),
    // ------
    Bench::spacer(),
    // ------
    Bench::new("binary_search: lookup non-existing high in many flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_SORTED).binary_search(&UNKNOWN_FLAG_HIGH)),
    Bench::new("binary_search: lookup non-existing low in many flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_SORTED).binary_search(&UNKNOWN_FLAG_LOW)),
    Bench::new("binary_search: lookup 'D' in many flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(MANY_FLAGS_SORTED).binary_search(black_box(&D_FLAG))),
    // ---
    Bench::new("binary_search: lookup non-existing high in few flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_SORTED).binary_search(&UNKNOWN_FLAG_HIGH)),
    Bench::new("binary_search: lookup non-existing low in few flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_SORTED).binary_search(&UNKNOWN_FLAG_LOW)),
    Bench::new("binary_search: lookup 'D' in few flags sorted")
        .with_samples(SAMPLES)
        .run(|| black_box(FEW_FLAGS_SORTED).binary_search(black_box(&D_FLAG))),
    // ---
    Bench::new("binary_search: lookup non-existing high in empty flags")
        .with_samples(SAMPLES)
        .run(|| black_box(EMPTY_FLAGS).binary_search(&UNKNOWN_FLAG_HIGH)),
    Bench::new("binary_search: lookup non-existing low in empty flags")
        .with_samples(SAMPLES)
        .run(|| black_box(EMPTY_FLAGS).binary_search(&UNKNOWN_FLAG_LOW)),
);
