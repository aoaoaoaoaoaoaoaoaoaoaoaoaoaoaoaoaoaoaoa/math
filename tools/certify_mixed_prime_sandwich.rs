use std::collections::HashSet;
use std::env;
use std::fs;

type Word = Vec<u8>;
type Signature<const N: usize> = [i16; N];

const ODD_FAMILY_LEFT_HEAD: &str = "DTTTTTTTTTTDDTDDTDDDDDDDDDT";
const ODD_FAMILY_RIGHT_HEAD: &str = "TTDDDDDDTTDDTDTDTDDTTDDTT";

const TRIGRAM_L32_02: Signature<8> = [-1, 1, 0, 0, 1, -1, 0, 0];
const TRIGRAM_L32_04: Signature<8> = [-1, 0, 2, -1, 0, 1, -1, 0];
const TRIGRAM_CATALOGUE_FNV64: u64 = 0x2db1_b99f_f029_2296;
const FOURGRAM_CATALOGUE_FNV64: u64 = 0xc644_4bcf_d9d0_55b4;

#[derive(Clone)]
struct PumpFamily {
    identifier: String,
    left: Word,
    right: Word,
    pump: Word,
    left_cut: usize,
    right_cut: usize,
}

#[derive(Clone)]
struct AddressBoundary {
    address: Word,
    suffix: Word,
    prefix: Word,
}

struct PhysicalCatalogues {
    trigrams: HashSet<Signature<8>>,
    fourgrams: HashSet<Signature<16>>,
    conditional_counts: [usize; 4],
    conditional_fourgrams: [HashSet<Signature<16>>; 4],
}

fn parse_word(text: &str) -> Word {
    text.bytes()
        .map(|letter| match letter {
            b'D' => 0,
            b'T' => 1,
            _ => panic!("mixed-prime word contains a non-D/T letter"),
        })
        .collect()
}

fn word_text(word: &[u8]) -> String {
    word.iter()
        .map(|&letter| match letter {
            0 => 'D',
            1 => 'T',
            _ => panic!("binary word contains a non-bit letter"),
        })
        .collect()
}

fn load_pump_families(path: &str) -> Vec<PumpFamily> {
    let manifest = fs::read_to_string(path).expect("cannot read the pump-family manifest");
    let mut lines = manifest.lines();
    assert_eq!(
        lines.next(),
        Some("identifier\tleft\tright\tpump\tleft_cut\tright_cut")
    );
    let mut families: Vec<_> = lines
        .map(|line| {
            let fields: Vec<_> = line.split('\t').collect();
            assert_eq!(fields.len(), 6, "malformed pump-family manifest row");
            PumpFamily {
                identifier: fields[0].to_owned(),
                left: parse_word(fields[1]),
                right: parse_word(fields[2]),
                pump: parse_word(fields[3]),
                left_cut: fields[4].parse().expect("invalid left pump cut"),
                right_cut: fields[5].parse().expect("invalid right pump cut"),
            }
        })
        .collect();
    assert_eq!(families.len(), 23);

    let odd_left_head = parse_word(ODD_FAMILY_LEFT_HEAD);
    let odd_right_head = parse_word(ODD_FAMILY_RIGHT_HEAD);
    let odd_left_cut = odd_left_head.len();
    let odd_right_cut = odd_right_head.len();
    let mut odd_left = odd_left_head;
    odd_left.extend(parse_word("DD"));
    let mut odd_right = odd_right_head;
    odd_right.extend(parse_word("DDTT"));
    families.push(PumpFamily {
        identifier: "odd".to_owned(),
        left: odd_left,
        right: odd_right,
        pump: parse_word("DT"),
        left_cut: odd_left_cut,
        right_cut: odd_right_cut,
    });

    let identifiers: HashSet<_> = families
        .iter()
        .map(|family| family.identifier.as_str())
        .collect();
    assert_eq!(identifiers.len(), 24);
    for family in &families {
        assert_eq!(family.left.len(), family.right.len());
        assert_eq!(family.pump.len(), 2);
        assert_eq!(family.pump.iter().sum::<u8>(), 1);
        assert!(family.left_cut <= family.left.len());
        assert!(family.right_cut <= family.right.len());
        assert_eq!(
            family.left.iter().sum::<u8>(),
            family.right.iter().sum::<u8>()
        );
    }
    assert_eq!(
        families.last().expect("odd family is present").left.len(),
        29
    );
    families
}

fn binary_words(length: usize) -> Vec<Word> {
    (0..1_usize << length)
        .map(|value| {
            (0..length)
                .rev()
                .map(|position| ((value >> position) & 1) as u8)
                .collect()
        })
        .collect()
}

fn boundary_representatives(factor_length: usize) -> Vec<Word> {
    // A length-r factor crossing a block boundary sees only the last and first r-1 letters.
    // Keep every shorter block verbatim. Replace a longer block by prefix_(r-1) ++
    // suffix_(r-1): the artificial middle seam contributes only internal block factors, whose
    // multiplicities cancel in yzxyx-xzyxy. Thus this finite set represents every nonempty
    // physical data-b, data-c, and toggle macro, not a bounded-length sample.
    let radius = factor_length - 1;
    let mut representatives = Vec::new();
    for length in 1..2 * radius {
        representatives.extend(binary_words(length));
    }
    for prefix in binary_words(radius) {
        for suffix in binary_words(radius) {
            let mut representative = prefix.clone();
            representative.extend(&suffix);
            representatives.push(representative);
        }
    }
    let distinct: HashSet<_> = representatives.iter().cloned().collect();
    assert_eq!(distinct.len(), representatives.len());
    representatives
}

fn factor_signature<const N: usize>(word: &[u8], factor_length: usize) -> Signature<N> {
    assert_eq!(N, 1_usize << factor_length);
    let mut signature = [0; N];
    for factor in word.windows(factor_length) {
        let coordinate = factor
            .iter()
            .fold(0_usize, |index, &letter| (index << 1) | letter as usize);
        signature[coordinate] += 1;
    }
    signature
}

fn subtract<const N: usize>(left: Signature<N>, right: Signature<N>) -> Signature<N> {
    std::array::from_fn(|coordinate| left[coordinate] - right[coordinate])
}

fn negate<const N: usize>(signature: Signature<N>) -> Signature<N> {
    signature.map(|value| -value)
}

fn concatenate(parts: &[&[u8]]) -> Word {
    let length = parts.iter().map(|part| part.len()).sum();
    let mut word = Vec::with_capacity(length);
    for part in parts {
        word.extend_from_slice(part);
    }
    word
}

fn physical_delta<const N: usize>(
    data_b: &[u8],
    data_c: &[u8],
    toggle: &[u8],
    factor_length: usize,
) -> Signature<N> {
    let flat = concatenate(&[data_c, toggle, data_b, data_c, data_b]);
    let nested = concatenate(&[data_b, toggle, data_c, data_b, data_c]);
    subtract(
        factor_signature(&flat, factor_length),
        factor_signature(&nested, factor_length),
    )
}

fn certify_physical_catalogues() -> PhysicalCatalogues {
    let representatives3 = boundary_representatives(3);
    let mut trigrams = HashSet::new();
    for data_b in &representatives3 {
        for data_c in &representatives3 {
            for toggle in &representatives3 {
                trigrams.insert(physical_delta(data_b, data_c, toggle, 3));
            }
        }
    }
    assert_eq!(representatives3.len(), 30);
    assert_eq!(trigrams.len(), 1_243);
    assert!(trigrams
        .iter()
        .all(|&signature| trigrams.contains(&negate(signature))));

    let conditional_trigrams = [
        TRIGRAM_L32_02,
        negate(TRIGRAM_L32_02),
        TRIGRAM_L32_04,
        negate(TRIGRAM_L32_04),
    ];
    let representatives4 = boundary_representatives(4);
    let mut fourgrams = HashSet::new();
    let mut conditional_counts = [0; 4];
    let mut conditional_fourgrams: [HashSet<Signature<16>>; 4] =
        std::array::from_fn(|_| HashSet::new());
    for data_b in &representatives4 {
        for data_c in &representatives4 {
            for toggle in &representatives4 {
                let fourgram = physical_delta(data_b, data_c, toggle, 4);
                let trigram = physical_delta(data_b, data_c, toggle, 3);
                fourgrams.insert(fourgram);
                for (index, target) in conditional_trigrams.iter().enumerate() {
                    if trigram == *target {
                        conditional_counts[index] += 1;
                        conditional_fourgrams[index].insert(fourgram);
                    }
                }
            }
        }
    }
    assert_eq!(representatives4.len(), 126);
    assert_eq!(fourgrams.len(), 93_463);
    assert_eq!(conditional_counts, [1_232, 1_232, 1_152, 1_152]);
    assert_eq!(
        conditional_fourgrams.each_ref().map(HashSet::len),
        [144, 144, 144, 144]
    );
    assert!(fourgrams
        .iter()
        .all(|&signature| fourgrams.contains(&negate(signature))));

    PhysicalCatalogues {
        trigrams,
        fourgrams,
        conditional_counts,
        conditional_fourgrams,
    }
}

fn expand_address(value: usize, depth: usize) -> Word {
    let mut address = Vec::with_capacity(2 * depth);
    for position in (0..depth).rev() {
        let macro_word = if (value >> position) & 1 == 0 {
            [0, 1]
        } else {
            [1, 0]
        };
        address.extend(macro_word);
    }
    address
}

fn boundary_pair(address: &[u8], radius: usize) -> (Word, Word) {
    if address.len() <= radius {
        (address.to_vec(), address.to_vec())
    } else {
        (
            address[address.len() - radius..].to_vec(),
            address[..radius].to_vec(),
        )
    }
}

fn address_boundaries(radius: usize) -> Vec<AddressBoundary> {
    let saturation_depth = match radius {
        2 => 2,
        3 => 4,
        _ => panic!("certificate only uses radii two and three"),
    };
    let mut boundaries = Vec::new();
    for depth in 0..=saturation_depth {
        for value in 0..1_usize << depth {
            let address = expand_address(value, depth);
            let (suffix, prefix) = boundary_pair(&address, radius);
            if boundaries.iter().any(|boundary: &AddressBoundary| {
                boundary.suffix == suffix && boundary.prefix == prefix
            }) {
                continue;
            }
            boundaries.push(AddressBoundary {
                address,
                suffix,
                prefix,
            });
        }
    }
    for depth in 0..=8 {
        for value in 0..1_usize << depth {
            let address = expand_address(value, depth);
            let pair = boundary_pair(&address, radius);
            assert!(boundaries
                .iter()
                .any(|boundary| (boundary.suffix.clone(), boundary.prefix.clone()) == pair));
        }
    }
    // For radius two, one first and one last address macro determine the boundary. For radius
    // three, two first and two last macros do; depth four makes those choices independent.
    // The replay above audits extraction, while this fixed-boundary argument proves saturation.
    boundaries
}

fn pumped_side(base: &[u8], cut: usize, pump: &[u8], depth: usize) -> Word {
    let mut word = Vec::with_capacity(base.len() + pump.len() * depth);
    word.extend_from_slice(&base[..cut]);
    for _ in 0..depth {
        word.extend_from_slice(pump);
    }
    word.extend_from_slice(&base[cut..]);
    word
}

fn pumped_pair(family: &PumpFamily, depth: usize) -> (Word, Word) {
    (
        pumped_side(&family.left, family.left_cut, &family.pump, depth),
        pumped_side(&family.right, family.right_cut, &family.pump, depth),
    )
}

fn reduced_sandwich_delta<const N: usize>(
    boundary: &AddressBoundary,
    left: &[u8],
    right: &[u8],
    factor_length: usize,
) -> Signature<N> {
    let left_context = concatenate(&[&boundary.suffix, left, &boundary.prefix]);
    let right_context = concatenate(&[&boundary.suffix, right, &boundary.prefix]);
    subtract(
        factor_signature(&left_context, factor_length),
        factor_signature(&right_context, factor_length),
    )
}

fn full_sandwich_delta<const N: usize>(
    address: &[u8],
    left: &[u8],
    right: &[u8],
    factor_length: usize,
) -> Signature<N> {
    let left_sandwich = concatenate(&[address, left, address]);
    let right_sandwich = concatenate(&[address, right, address]);
    subtract(
        factor_signature(&left_sandwich, factor_length),
        factor_signature(&right_sandwich, factor_length),
    )
}

fn contextual_side(
    boundary: &AddressBoundary,
    family: &PumpFamily,
    left: bool,
    depth: usize,
) -> Word {
    let (base, cut) = if left {
        (&family.left, family.left_cut)
    } else {
        (&family.right, family.right_cut)
    };
    let middle = pumped_side(base, cut, &family.pump, depth);
    concatenate(&[&boundary.suffix, &middle, &boundary.prefix])
}

fn periodic_increment<const N: usize>(
    pump: &[u8],
    factor_length: usize,
    threshold: usize,
) -> Signature<N> {
    let shorter = pumped_side(&[], 0, pump, threshold);
    let longer = pumped_side(&[], 0, pump, threshold + 1);
    subtract(
        factor_signature(&longer, factor_length),
        factor_signature(&shorter, factor_length),
    )
}

fn certify_pump_locality<const N: usize>(
    families: &[PumpFamily],
    boundaries: &[AddressBoundary],
    factor_length: usize,
) {
    let radius = factor_length - 1;
    let threshold = radius.div_ceil(2);
    // At k>=threshold, |S^k|>=r-1, so no r-factor meets both pump seams. The fixed aligned
    // prefix/suffix of S^k freezes the two seam contributions. Extending S^k by one two-letter
    // period adds the same two internal periodic factors on both relation sides, so the target
    // discrepancy is constant for every later k. The two displayed increments instantiate the
    // premise and independently replay its first consequence; they are not a depth cutoff.
    for family in families {
        let increment = periodic_increment::<N>(&family.pump, factor_length, threshold);
        for boundary in boundaries {
            for left in [true, false] {
                let at_threshold = contextual_side(boundary, family, left, threshold);
                let successor = contextual_side(boundary, family, left, threshold + 1);
                let next = contextual_side(boundary, family, left, threshold + 2);
                assert_eq!(
                    subtract::<N>(
                        factor_signature::<N>(&successor, factor_length),
                        factor_signature::<N>(&at_threshold, factor_length),
                    ),
                    increment
                );
                assert_eq!(
                    subtract::<N>(
                        factor_signature::<N>(&next, factor_length),
                        factor_signature::<N>(&successor, factor_length),
                    ),
                    increment
                );
            }
            let (left, right) = pumped_pair(family, threshold);
            let stable = reduced_sandwich_delta::<N>(boundary, &left, &right, factor_length);
            for depth in threshold + 1..=threshold + 2 {
                let (later_left, later_right) = pumped_pair(family, depth);
                assert_eq!(
                    reduced_sandwich_delta::<N>(boundary, &later_left, &later_right, factor_length,),
                    stable
                );
            }
        }
    }
}

fn certify_boundary_reduction<const N: usize>(
    families: &[PumpFamily],
    boundaries: &[AddressBoundary],
    factor_length: usize,
) {
    let threshold = (factor_length - 1).div_ceil(2);
    for family in families {
        for depth in [0, threshold] {
            let (left, right) = pumped_pair(family, depth);
            for boundary in boundaries {
                assert_eq!(
                    full_sandwich_delta::<N>(&boundary.address, &left, &right, factor_length,),
                    reduced_sandwich_delta::<N>(boundary, &left, &right, factor_length)
                );
            }
        }
    }
}

#[derive(Debug)]
struct TrigramSurvivor {
    family: String,
    stable: bool,
    suffix: String,
    prefix: String,
    target: Signature<8>,
}

fn trigram_survivors(
    families: &[PumpFamily],
    boundaries: &[AddressBoundary],
    physical: &HashSet<Signature<8>>,
) -> Vec<TrigramSurvivor> {
    let mut survivors = Vec::new();
    for family in families {
        for (depth, stable) in [(0, false), (1, true)] {
            let (left, right) = pumped_pair(family, depth);
            for boundary in boundaries {
                let target = reduced_sandwich_delta(boundary, &left, &right, 3);
                if physical.contains(&target) {
                    survivors.push(TrigramSurvivor {
                        family: family.identifier.clone(),
                        stable,
                        suffix: word_text(&boundary.suffix),
                        prefix: word_text(&boundary.prefix),
                        target,
                    });
                }
            }
        }
    }
    survivors
}

fn assert_trigram_survivors(survivors: &[TrigramSurvivor]) {
    assert_eq!(survivors.len(), 3);
    assert!(survivors.iter().any(|row| {
        row.family == "l32-02"
            && !row.stable
            && row.suffix == "DT"
            && row.prefix == "TD"
            && row.target == TRIGRAM_L32_02
    }));
    for stable in [false, true] {
        assert!(survivors.iter().any(|row| {
            row.family == "l32-04"
                && row.stable == stable
                && row.suffix == "DT"
                && row.prefix == "DT"
                && row.target == TRIGRAM_L32_04
        }));
    }
}

fn family<'a>(families: &'a [PumpFamily], identifier: &str) -> &'a PumpFamily {
    families
        .iter()
        .find(|family| family.identifier == identifier)
        .expect("named pump family is present")
}

fn boundary_refines(boundary: &AddressBoundary, suffix: &[u8], prefix: &[u8]) -> bool {
    boundary.suffix.ends_with(suffix) && boundary.prefix.starts_with(prefix)
}

fn fourgram_extinction(
    families: &[PumpFamily],
    boundaries: &[AddressBoundary],
    catalogues: &PhysicalCatalogues,
) -> (usize, usize) {
    let suffix_dt = parse_word("DT");
    let prefix_td = parse_word("TD");
    let family02 = family(families, "l32-02");
    let (left02, right02) = pumped_pair(family02, 0);
    let contexts02: Vec<_> = boundaries
        .iter()
        .filter(|boundary| boundary_refines(boundary, &suffix_dt, &prefix_td))
        .collect();
    assert_eq!(contexts02.len(), 4);
    let targets02: HashSet<_> = contexts02
        .iter()
        .map(|boundary| reduced_sandwich_delta(boundary, &left02, &right02, 4))
        .collect();
    let expected02: HashSet<_> = [
        [-1, 0, 1, 0, 0, 0, 2, -2, 0, 1, -1, 0, 1, -1, -2, 2],
        [-1, 0, 0, 1, 0, 0, 2, -2, 0, 1, 0, -1, 1, -1, -2, 2],
        [-1, 0, 1, 0, 1, -1, 2, -2, 0, 1, -1, 0, 0, 0, -2, 2],
        [-1, 0, 0, 1, 1, -1, 2, -2, 0, 1, 0, -1, 0, 0, -2, 2],
    ]
    .into_iter()
    .collect();
    assert_eq!(targets02, expected02);
    assert!(targets02.iter().all(|target| {
        !catalogues.fourgrams.contains(target)
            && !catalogues.conditional_fourgrams[0].contains(target)
            && !catalogues.fourgrams.contains(&negate(*target))
            && !catalogues.conditional_fourgrams[1].contains(&negate(*target))
    }));

    let prefix_dt = parse_word("DT");
    let family04 = family(families, "l32-04");
    let contexts04: Vec<_> = boundaries
        .iter()
        .filter(|boundary| boundary_refines(boundary, &suffix_dt, &prefix_dt))
        .collect();
    assert_eq!(contexts04.len(), 5);
    let pairs04: Vec<_> = (0..=2).map(|depth| pumped_pair(family04, depth)).collect();
    let mut targets04 = HashSet::new();
    for boundary in &contexts04 {
        let target = reduced_sandwich_delta(boundary, &pairs04[0].0, &pairs04[0].1, 4);
        for (left, right) in &pairs04[1..] {
            assert_eq!(reduced_sandwich_delta(boundary, left, right, 4), target);
        }
        assert!(!catalogues.fourgrams.contains(&target));
        assert!(!catalogues.conditional_fourgrams[2].contains(&target));
        assert!(!catalogues.fourgrams.contains(&negate(target)));
        assert!(!catalogues.conditional_fourgrams[3].contains(&negate(target)));
        targets04.insert(target);
    }
    let expected04: HashSet<_> = [
        [-1, 0, 1, -2, 0, 2, 1, -2, 0, 0, 0, 2, 0, -1, -2, 2],
        [-1, 0, 2, -2, 0, 2, 1, -2, 0, 0, 0, 1, 0, -1, -2, 2],
        [-1, 0, 3, -3, 0, 2, 1, -2, 0, 0, -1, 2, 0, -1, -2, 2],
        [-1, 0, 1, -1, 0, 2, 1, -2, 0, 0, 1, 0, 0, -1, -2, 2],
    ]
    .into_iter()
    .collect();
    assert_eq!(targets04, expected04);

    (contexts02.len() + contexts04.len(), 4 + 5 + 5)
}

fn fnv_byte(hash: &mut u64, byte: u8) {
    *hash ^= u64::from(byte);
    *hash = hash.wrapping_mul(1_099_511_628_211);
}

fn fingerprint_set<const N: usize>(set: &HashSet<Signature<N>>) -> u64 {
    let mut rows: Vec<_> = set.iter().copied().collect();
    rows.sort_unstable();
    let mut hash = 14_695_981_039_346_656_037;
    for byte in (rows.len() as u64).to_le_bytes() {
        fnv_byte(&mut hash, byte);
    }
    for row in rows {
        for coordinate in row {
            for byte in coordinate.to_le_bytes() {
                fnv_byte(&mut hash, byte);
            }
        }
    }
    hash
}

fn main() {
    let arguments: Vec<_> = env::args().skip(1).collect();
    assert_eq!(arguments.len(), 1, "usage: CERTIFIER PUMP_MANIFEST");
    let families = load_pump_families(&arguments[0]);
    let boundaries3 = address_boundaries(2);
    let boundaries4 = address_boundaries(3);
    assert_eq!(boundaries3.len(), 5);
    assert_eq!(boundaries4.len(), 19);

    certify_boundary_reduction::<8>(&families, &boundaries3, 3);
    certify_boundary_reduction::<16>(&families, &boundaries4, 4);
    certify_pump_locality::<8>(&families, &boundaries3, 3);
    certify_pump_locality::<16>(&families, &boundaries4, 4);

    let catalogues = certify_physical_catalogues();
    let survivors = trigram_survivors(&families, &boundaries3, &catalogues.trigrams);
    assert_trigram_survivors(&survivors);
    let (fourgram_boundary_cells, fourgram_logical_cells) =
        fourgram_extinction(&families, &boundaries4, &catalogues);

    let trigram_fingerprint = fingerprint_set(&catalogues.trigrams);
    let fourgram_fingerprint = fingerprint_set(&catalogues.fourgrams);
    assert_eq!(trigram_fingerprint, TRIGRAM_CATALOGUE_FNV64);
    assert_eq!(fourgram_fingerprint, FOURGRAM_CATALOGUE_FNV64);
    println!(
        concat!(
            "{{\"families\":{},\"trigram_representatives\":30,",
            "\"trigram_physical_deltas\":{},\"trigram_forward_cells\":{},",
            "\"trigram_survivors\":{},\"fourgram_representatives\":126,",
            "\"fourgram_physical_deltas\":{},\"fourgram_forward_boundary_cells\":{},",
            "\"fourgram_forward_logical_cells\":{},\"fourgram_both_orientation_cells\":{},",
            "\"conditional_counts\":{:?},",
            "\"trigram_fnv64\":\"{:016x}\",\"fourgram_fnv64\":\"{:016x}\",",
            "\"status\":\"all 24 explicit sandwich families are impossible\"}}"
        ),
        families.len(),
        catalogues.trigrams.len(),
        families.len() * 2 * boundaries3.len(),
        survivors.len(),
        catalogues.fourgrams.len(),
        fourgram_boundary_cells,
        fourgram_logical_cells,
        2 * fourgram_logical_cells,
        catalogues.conditional_counts,
        trigram_fingerprint,
        fourgram_fingerprint,
    );
}
