use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::time::Instant;

#[derive(Clone, Copy)]
struct Rule {
    name: &'static str,
    larger: &'static str,
    smaller: &'static str,
}

const RULES: [Rule; 5] = [
    Rule {
        name: "r27",
        larger: "TTDDDDDDTTDDTDTDTDDTTDDTDTT",
        smaller: "DTTTTTTTTTTDDTDDTDDDDDDDDDD",
    },
    Rule {
        name: "r29",
        larger: "TTDDDDDDTTDDTDTDTDDTTDDTTDDTT",
        smaller: "DTTTTTTTTTTDDTDDTDDDDDDDDDTDD",
    },
    Rule {
        name: "r30a",
        larger: "TTDDDDDDDDTTTTDTDTDDTDDTDDTDTT",
        smaller: "DTTTTTTDTTDTTTDDTDDTDDDDDDDDDD",
    },
    Rule {
        name: "r30b",
        larger: "TTDDDDDDDDDDTTTDDDTTTTDDTDDDTT",
        smaller: "DTTTTTTDDTDTTDDTTDDTDDDDDDDDDD",
    },
    Rule {
        name: "r30c",
        larger: "TTDDDDDDDDDTDTTDTTTTDDTDDTDDDT",
        smaller: "DTTTTTTDDTTTDDDTDTDTDDDDDDDDDD",
    },
];

const ODD_FAMILY_LEFT_HEAD: &str = "DTTTTTTTTTTDDTDDTDDDDDDDDDT";
const ODD_FAMILY_RIGHT_HEAD: &str = "TTDDDDDDTTDDTDTDTDDTTDDTT";

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Matrix([[u128; 2]; 2]);

impl Matrix {
    const IDENTITY: Self = Self([[1, 0], [0, 1]]);
    const DILATE: Self = Self([[2, 0], [0, 3]]);
    const TRANSLATE: Self = Self([[3, 5], [0, 5]]);

    fn checked_mul(self, right: Self) -> Self {
        let mut product = [[0_u128; 2]; 2];
        for (row, product_row) in product.iter_mut().enumerate() {
            for (column, product_entry) in product_row.iter_mut().enumerate() {
                for inner in 0..2 {
                    *product_entry = (*product_entry)
                        .checked_add(
                            self.0[row][inner]
                                .checked_mul(right.0[inner][column])
                                .expect("matrix product exceeds u128"),
                        )
                        .expect("matrix product exceeds u128");
                }
            }
        }
        Self(product)
    }
}

fn generator(letter: u8) -> Matrix {
    match letter {
        b'D' => Matrix::DILATE,
        b'T' => Matrix::TRANSLATE,
        _ => panic!("raw words use only D and T"),
    }
}

fn word_matrix(word: &str) -> Matrix {
    word.bytes().fold(Matrix::IDENTITY, |product, letter| {
        product.checked_mul(generator(letter))
    })
}

fn bit_word_matrix(word: u64, length: usize) -> Matrix {
    (0..length).rev().fold(Matrix::IDENTITY, |product, shift| {
        let letter = if word & (1_u64 << shift) == 0 {
            Matrix::DILATE
        } else {
            Matrix::TRANSLATE
        };
        product.checked_mul(letter)
    })
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Signature {
    dilates: usize,
    translates: usize,
    offset: u128,
}

fn bit_signature(word: u64, length: usize) -> Signature {
    let (mut dilates, mut translates, mut slope_numerator, mut offset) = (0, 0, 1_u128, 0_u128);
    for shift in (0..length).rev() {
        if word & (1_u64 << shift) == 0 {
            dilates += 1;
            slope_numerator *= 2;
            offset *= 3;
        } else {
            translates += 1;
            offset = 5 * (slope_numerator + offset);
            slope_numerator *= 3;
        }
    }
    Signature {
        dilates,
        translates,
        offset,
    }
}

fn word_string(word: u64, length: usize) -> String {
    let mut text = String::with_capacity(length);
    for shift in (0..length).rev() {
        text.push(if word & (1_u64 << shift) == 0 {
            'D'
        } else {
            'T'
        });
    }
    text
}

fn normalize_text(mut text: String, rules: &[Rule]) -> String {
    loop {
        let redex = rules
            .iter()
            .filter_map(|rule| {
                text.find(rule.larger)
                    .map(|position| (position, rule.larger, rule.smaller))
            })
            .min_by_key(|&(position, _, _)| position);
        let Some((position, larger, smaller)) = redex else {
            return text;
        };
        text.replace_range(position..position + larger.len(), smaller);
    }
}

fn normalize(word: u64, length: usize, rules: &[Rule]) -> String {
    normalize_text(word_string(word, length), rules)
}

fn odd_family(pump: usize) -> (String, String) {
    let spine = "DT".repeat(pump);
    (
        format!("{ODD_FAMILY_LEFT_HEAD}{spine}DD"),
        format!("{ODD_FAMILY_RIGHT_HEAD}{spine}DDTT"),
    )
}

fn binomial(n: usize, k: usize) -> u64 {
    let k = k.min(n - k);
    let mut value = 1_u128;
    for index in 0..k {
        value = value * (n - index) as u128 / (index + 1) as u128;
    }
    value.try_into().expect("census cardinality exceeds u64")
}

struct Enumeration {
    length: usize,
    packed: Vec<u128>,
}

impl Enumeration {
    fn descend(
        &mut self,
        position: usize,
        dilates_remaining: usize,
        slope_numerator: u128,
        offset: u128,
        word: u64,
    ) {
        let slots = self.length - position;
        if dilates_remaining > slots {
            return;
        }
        if position == self.length {
            assert_eq!(dilates_remaining, 0);
            assert!(offset < (1_u128 << (128 - self.length)));
            self.packed.push((offset << self.length) | word as u128);
            return;
        }
        if dilates_remaining > 0 {
            self.descend(
                position + 1,
                dilates_remaining - 1,
                2 * slope_numerator,
                3 * offset,
                word << 1,
            );
        }
        if dilates_remaining < slots {
            self.descend(
                position + 1,
                dilates_remaining,
                3 * slope_numerator,
                5 * (slope_numerator + offset),
                (word << 1) | 1,
            );
        }
    }
}

#[derive(Default)]
struct Census {
    words: u64,
    classes: u64,
    generated_duplicates: u64,
    independent_duplicates: u64,
    independent_pairs: Vec<(String, String, u128)>,
}

fn census_group(length: usize, dilates: usize, rules: &[Rule]) -> Census {
    let words = binomial(length, dilates);
    let mut enumeration = Enumeration {
        length,
        packed: Vec::with_capacity(words.try_into().expect("capacity exceeds usize")),
    };
    enumeration.descend(0, dilates, 1, 0, 0);
    assert_eq!(enumeration.packed.len() as u64, words);
    enumeration.packed.sort_unstable();

    let word_mask = (1_u128 << length) - 1;
    let mut result = Census {
        words,
        ..Census::default()
    };
    let mut start = 0;
    while start < enumeration.packed.len() {
        let offset = enumeration.packed[start] >> length;
        let mut end = start + 1;
        while end < enumeration.packed.len() && enumeration.packed[end] >> length == offset {
            end += 1;
        }
        result.classes += 1;
        if end - start > 1 {
            let mut forms: Vec<(String, String)> = enumeration.packed[start..end]
                .iter()
                .map(|packed| {
                    let word = (packed & word_mask) as u64;
                    (normalize(word, length, rules), word_string(word, length))
                })
                .collect();
            forms.sort_unstable();
            let mut distinct_forms = 1_u64;
            for index in 1..forms.len() {
                if forms[index - 1].0 != forms[index].0 {
                    distinct_forms += 1;
                    result.independent_pairs.push((
                        forms[index - 1].1.clone(),
                        forms[index].1.clone(),
                        offset,
                    ));
                }
            }
            result.generated_duplicates += (end - start) as u64 - distinct_forms;
            result.independent_duplicates += distinct_forms - 1;
        }
        start = end;
    }
    result
}

fn census(length: usize, rules: &[Rule], print: bool) -> Census {
    assert!((1..=31).contains(&length));
    let critical_report = critical_pairs(rules, false, false);
    let congruence_deciding =
        critical_report.inclusions == 0 && length < critical_report.minimum_length;
    assert!(congruence_deciding);
    let started = Instant::now();
    let mut total = Census::default();
    for dilates in 0..=length {
        let group_started = Instant::now();
        let result = census_group(length, dilates, rules);
        if print && (result.generated_duplicates > 0 || result.independent_duplicates > 0) {
            println!(
                "GROUP\tlength={length}\tD={dilates}\tT={}\twords={}\tclasses={}\tgenerated_dup={}\tindependent_dup={}\tms={}",
                length - dilates,
                result.words,
                result.classes,
                result.generated_duplicates,
                result.independent_duplicates,
                group_started.elapsed().as_millis(),
            );
            for (left, right, offset) in &result.independent_pairs {
                println!("INDEPENDENT\toffset={offset}\n  {left}\n  {right}");
            }
        }
        total.words += result.words;
        total.classes += result.classes;
        total.generated_duplicates += result.generated_duplicates;
        total.independent_duplicates += result.independent_duplicates;
        total.independent_pairs.extend(result.independent_pairs);
    }
    if print {
        println!(
            "TOTAL\tlength={length}\trules={}\twords={}\tclasses={}\tgenerated_dup={}\tindependent_dup={}\tcongruence_deciding_nf={congruence_deciding}\tcritical_min={}\tms={}",
            rules.len(),
            total.words,
            total.classes,
            total.generated_duplicates,
            total.independent_duplicates,
            critical_report.minimum_length,
            started.elapsed().as_millis(),
        );
    }
    total
}

fn occurrences(word: &str, pattern: &str) -> Vec<usize> {
    if pattern.len() > word.len() {
        return Vec::new();
    }
    (0..=word.len() - pattern.len())
        .filter(|&position| word[position..].starts_with(pattern))
        .collect()
}

fn reductions(word: &str, rules: &[Rule]) -> Vec<String> {
    let mut descendants = BTreeSet::new();
    for rule in rules {
        for position in occurrences(word, rule.larger) {
            let mut descendant = String::with_capacity(word.len());
            descendant.push_str(&word[..position]);
            descendant.push_str(rule.smaller);
            descendant.push_str(&word[position + rule.larger.len()..]);
            assert!(descendant.as_str() < word);
            descendants.insert(descendant);
        }
    }
    descendants.into_iter().collect()
}

fn normal_forms(
    word: &str,
    rules: &[Rule],
    memo: &mut HashMap<String, BTreeSet<String>>,
) -> BTreeSet<String> {
    if let Some(forms) = memo.get(word) {
        return forms.clone();
    }
    let descendants = reductions(word, rules);
    let forms = if descendants.is_empty() {
        BTreeSet::from([word.to_owned()])
    } else {
        descendants
            .iter()
            .flat_map(|descendant| normal_forms(descendant, rules, memo))
            .collect()
    };
    memo.insert(word.to_owned(), forms.clone());
    forms
}

struct CriticalReport {
    overlaps: usize,
    inclusions: usize,
    joinable: usize,
    minimum_length: usize,
}

fn critical_pairs(rules: &[Rule], verbose: bool, print: bool) -> CriticalReport {
    let mut memo = HashMap::new();
    let mut overlaps = 0;
    let mut inclusions = 0;
    let mut joinable = 0;
    let mut minimum_length = usize::MAX;
    let mut length_counts = BTreeMap::<usize, usize>::new();

    for (outer_index, outer) in rules.iter().enumerate() {
        for (inner_index, inner) in rules.iter().enumerate() {
            for position in occurrences(outer.larger, inner.larger) {
                if outer_index != inner_index || position != 0 {
                    inclusions += 1;
                }
            }
        }
    }

    for first in rules {
        for second in rules {
            let limit = first.larger.len().min(second.larger.len());
            for overlap in 1..limit {
                if first.larger[first.larger.len() - overlap..] != second.larger[..overlap] {
                    continue;
                }
                overlaps += 1;
                let source = format!("{}{}", first.larger, &second.larger[overlap..]);
                let left_branch = format!("{}{}", first.smaller, &second.larger[overlap..]);
                let right_branch = format!(
                    "{}{}",
                    &first.larger[..first.larger.len() - overlap],
                    second.smaller,
                );
                let left_forms = normal_forms(&left_branch, rules, &mut memo);
                let right_forms = normal_forms(&right_branch, rules, &mut memo);
                let is_joinable = left_forms.iter().any(|form| right_forms.contains(form));
                joinable += usize::from(is_joinable);
                minimum_length = minimum_length.min(source.len());
                *length_counts.entry(source.len()).or_default() += 1;
                assert_eq!(word_matrix(&source), word_matrix(&left_branch));
                assert_eq!(word_matrix(&source), word_matrix(&right_branch));
                if print {
                    println!(
                        "CRITICAL\t{}->{}\toverlap={overlap}\tlength={}\tjoinable={is_joinable}\tleft_nf={}\tright_nf={}",
                        first.name,
                        second.name,
                        source.len(),
                        left_forms.len(),
                        right_forms.len(),
                    );
                }
                if print && verbose {
                    for form in &left_forms {
                        println!("  L {form}");
                    }
                    for form in &right_forms {
                        println!("  R {form}");
                    }
                }
            }
        }
    }
    if print {
        println!(
            "CRITICAL_TOTAL\trules={}\toverlaps={overlaps}\tinclusions={inclusions}\tjoinable={joinable}\tunjoinable={}\tminimum_length={minimum_length}\tlength_histogram={length_counts:?}",
            rules.len(),
            overlaps - joinable,
        );
    }
    CriticalReport {
        overlaps,
        inclusions,
        joinable,
        minimum_length,
    }
}

fn self_check() {
    for rule in RULES {
        assert_eq!(rule.larger.len(), rule.smaller.len());
        assert!(rule.larger > rule.smaller);
        assert_eq!(word_matrix(rule.larger), word_matrix(rule.smaller));
    }

    for length in 1..=12 {
        let mut matrix_classes = BTreeSet::new();
        let mut signature_classes = BTreeSet::new();
        for word in 0..1_u64 << length {
            let matrix = bit_word_matrix(word, length);
            let signature = bit_signature(word, length);
            assert_eq!(matrix.0[0][1], signature.offset);
            assert_eq!(matrix.0[1][0], 0);
            assert_eq!(
                matrix.0[0][0],
                2_u128.pow(signature.dilates as u32) * 3_u128.pow(signature.translates as u32),
            );
            assert_eq!(
                matrix.0[1][1],
                3_u128.pow(signature.dilates as u32) * 5_u128.pow(signature.translates as u32),
            );
            matrix_classes.insert(matrix);
            signature_classes.insert(signature);
        }
        assert_eq!(matrix_classes.len(), signature_classes.len());
        let optimized = census(length, &RULES, false);
        assert_eq!(optimized.words, 1_u64 << length);
        assert_eq!(optimized.classes as usize, matrix_classes.len());
        assert_eq!(optimized.generated_duplicates, 0);
        assert_eq!(optimized.independent_duplicates, 0);
    }

    let two_rule_report = critical_pairs(&RULES[..2], false, false);
    assert_eq!(two_rule_report.overlaps, 8);
    assert_eq!(two_rule_report.inclusions, 0);
    assert_eq!(two_rule_report.joinable, 0);
    assert_eq!(two_rule_report.minimum_length, 52);
    let five_rule_report = critical_pairs(&RULES, false, false);
    assert_eq!(five_rule_report.overlaps, 45);
    assert_eq!(five_rule_report.inclusions, 0);
    assert_eq!(five_rule_report.joinable, 0);
    assert_eq!(five_rule_report.minimum_length, 52);

    for pump in 0..=11 {
        let (left, right) = odd_family(pump);
        assert_eq!(left.len(), 29 + 2 * pump);
        assert_eq!(right.len(), 29 + 2 * pump);
        assert_ne!(left, right);
        assert_eq!(word_matrix(&left), word_matrix(&right));
        let left_normal = normalize_text(left.clone(), &RULES);
        let right_normal = normalize_text(right.clone(), &RULES);
        if pump == 0 {
            assert_eq!(left_normal, right_normal);
        } else {
            assert_eq!(left_normal, left);
            assert_eq!(right_normal, right);
        }
    }
    println!("SELF_CHECK\tlengths=1..12\trules=5\todd_family=0..11\tstatus=ok");
}

fn selected_rules(argument: Option<&String>) -> &'static [Rule] {
    let count = argument.map_or(RULES.len(), |value| {
        value.parse().expect("RULE_COUNT must be an integer")
    });
    assert!((1..=RULES.len()).contains(&count));
    &RULES[..count]
}

fn main() {
    let arguments: Vec<String> = env::args().skip(1).collect();
    match arguments.first().map(String::as_str) {
        Some("self-check") if arguments.len() == 1 => self_check(),
        Some("census") if (2..=3).contains(&arguments.len()) => {
            let length = arguments[1]
                .parse()
                .expect("LENGTH must be an integer from 1 through 31");
            census(length, selected_rules(arguments.get(2)), true);
        }
        Some("critical") if arguments.len() <= 3 => {
            let rules = selected_rules(
                arguments
                    .get(1)
                    .filter(|value| value.as_str() != "--verbose"),
            );
            let verbose = arguments.iter().any(|argument| argument == "--verbose");
            critical_pairs(rules, verbose, true);
        }
        _ => {
            eprintln!(
                "usage:\n  mixed-prime-kernel-audit self-check\n  mixed-prime-kernel-audit census LENGTH [RULE_COUNT]\n  mixed-prime-kernel-audit critical [RULE_COUNT] [--verbose]"
            );
            std::process::exit(2);
        }
    }
}
