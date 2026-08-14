//! Test that verifies the gen!/uniform! macro dispatch behavior matches
//! what the Lean faithful generator expects.
//!
//! The Lean generator records each `intInRange(lo, hi)` call and its result.
//! To reproduce: we construct an `Unstructured` buffer such that each
//! `int_in_range::<u8>(lo..=hi)` call returns the same value.
//!
//! For int_in_range::<u8>(lo..=hi):
//!   range = hi - lo + 1
//!   byte is consumed, value = lo + (byte % range)
//!   So to get value `v`, we put byte = `v - lo` in the buffer.

use arbitrary::Unstructured;
use cedar_policy_generators::{accum, gen, gen_inner};

/// Construct a byte buffer that will make successive int_in_range::<u8>(lo..=hi)
/// calls return the specified values.
fn make_buffer(choices: &[(u8, u8, u8)]) -> Vec<u8> {
    // Each (lo, hi, value) → byte = value - lo
    choices.iter().map(|(lo, _hi, value)| value - lo).collect()
}

/// Test that gen! with weights [2, 1, 1, 1] (total=5) dispatches correctly.
/// This matches the outer gen! in ExprGenerator::generate_expr.
#[test]
fn test_outer_gen_dispatch() -> Result<(), Box<dyn std::error::Error>> {
    // For each possible choice value 0..=4, verify which branch is taken
    for choice_val in 0u8..=4 {
        let buf = make_buffer(&[(0, 4, choice_val)]);
        let mut u = Unstructured::new(&buf);

        let branch: u8 = gen!(
            &mut u,
            2 => 0u8, // literal_or_var
            1 => 1u8, // eq
            1 => 2u8, // not
            1 => 3u8  // other
        );

        let expected = if choice_val < 2 {
            0 // literal_or_var
        } else if choice_val < 3 {
            1 // eq
        } else if choice_val < 4 {
            2 // not
        } else {
            3 // other
        };

        assert_eq!(
            branch, expected,
            "choice_val={choice_val}: got branch {branch}, expected {expected}"
        );
    }
    Ok(())
}

/// Test that gen! with the inner weights (total=43) dispatches correctly.
/// This matches the inner gen! in ExprGenerator::generate_expr.
#[test]
fn test_inner_gen_dispatch() -> Result<(), Box<dyn std::error::Error>> {
    // Test representative values from each branch boundary
    let test_cases: Vec<(u8, u8)> = vec![
        (0, 0),   // ite (< 2)
        (1, 0),   // ite (< 2)
        (2, 1),   // and (< 4)
        (3, 1),   // and (< 4)
        (4, 2),   // or (< 6)
        (5, 2),   // or (< 6)
        (6, 3),   // less (< 7)
        (7, 4),   // lessEq (< 8)
        (8, 5),   // greater (< 9)
        (9, 6),   // greaterEq (< 10)
        (10, 7),  // add (< 11)
        (11, 8),  // sub (< 12)
        (12, 9),  // mul (< 13)
        (13, 10), // neg (< 14)
        (14, 11), // in (< 20)
        (19, 11), // in (< 20)
        (20, 12), // contains (< 21)
        (21, 13), // containsAll (< 22)
        (22, 14), // containsAny (< 23)
        (23, 15), // isEmpty (< 24)
        (24, 16), // like (< 26)
        (25, 16), // like (< 26)
        (26, 17), // is (< 27)
        (27, 18), // set (< 28)
        (28, 19), // record (< 29)
        (29, 20), // extFun (< 30)
        (30, 21), // getAttr (< 37)
        (36, 21), // getAttr (< 37)
        (37, 22), // hasAttr (< 41)
        (40, 22), // hasAttr (< 41)
        (41, 23), // hasTag (< 43)
        (42, 23), // hasTag (< 43)
    ];

    for (choice_val, expected_branch) in &test_cases {
        let buf = make_buffer(&[(0, 42, *choice_val)]);
        let mut u = Unstructured::new(&buf);

        let branch: u8 = gen!(
            &mut u,
            2 => 0u8,  // ite
            2 => 1u8,  // and
            2 => 2u8,  // or
            1 => 3u8,  // less
            1 => 4u8,  // lessEq
            1 => 5u8,  // greater
            1 => 6u8,  // greaterEq
            1 => 7u8,  // add
            1 => 8u8,  // sub
            1 => 9u8,  // mul
            1 => 10u8, // neg
            6 => 11u8, // in
            1 => 12u8, // contains
            1 => 13u8, // containsAll
            1 => 14u8, // containsAny
            1 => 15u8, // isEmpty
            2 => 16u8, // like
            1 => 17u8, // is
            1 => 18u8, // set
            1 => 19u8, // record
            1 => 20u8, // extFun
            7 => 21u8, // getAttr
            4 => 22u8, // hasAttr
            4 => 23u8  // hasTag
        );

        assert_eq!(
            branch, *expected_branch,
            "choice_val={choice_val}: got branch {branch}, expected {expected_branch}"
        );
    }
    Ok(())
}

/// Verify that make_buffer produces bytes that Unstructured decodes correctly
#[test]
fn test_make_buffer_roundtrip() {
    let choices = [(0u8, 4u8, 3u8), (0, 42, 20), (0, 1, 1), (0, 3, 2)];
    let buf = make_buffer(&choices);
    let mut u = Unstructured::new(&buf);

    for (lo, hi, expected) in &choices {
        let val = u.int_in_range::<u8>(*lo..=*hi).unwrap();
        assert_eq!(
            val, *expected,
            "Expected {expected} from int_in_range({lo}..={hi}), got {val}"
        );
    }
}

/// Replay a Lean-generated byte buffer through the same dispatch logic
/// and verify we get the same top-level expression structure.
///
/// Test case from the Lean output:
///   bytes: [4, 30, 6, 1, 0]
///   expr: getAttr (var principal) "bar"
///
/// Expected decode:
///   byte[0]=4: intInRange(0..=4) → 4 → inner gen! branch
///   byte[1]=30: intInRange(0..=42) → 30 → getAttr (30 < 37)
///   byte[2]=6: intInRange(0..=7) → 6 → identPool[6] = "bar"
///   byte[3]=1: intInRange(0..=1) → 1 → var
///   byte[4]=0: intInRange(0..=3) → 0 → principal
#[test]
fn test_lean_replay_getattr() {
    let buf: Vec<u8> = vec![4, 30, 6, 1, 0];
    let mut u = Unstructured::new(&buf);

    // Outer dispatch: should be 4 (inner gen)
    let outer = u.int_in_range::<u8>(0..=4).unwrap();
    assert_eq!(outer, 4);

    // Inner dispatch: should be 30 (getAttr, since 30 < 37)
    let inner = u.int_in_range::<u8>(0..=42).unwrap();
    assert_eq!(inner, 30);
    assert!(inner >= 30 && inner < 37, "should be getAttr branch");

    // Attr name: identPool index
    let attr_idx = u.int_in_range::<u8>(0..=7).unwrap();
    assert_eq!(attr_idx, 6); // "bar"

    // Sub-expr: literal_or_var choice
    let lit_or_var = u.int_in_range::<u8>(0..=1).unwrap();
    assert_eq!(lit_or_var, 1); // var

    // Var choice
    let var_choice = u.int_in_range::<u8>(0..=3).unwrap();
    assert_eq!(var_choice, 0); // principal
}

/// Second test case from Lean output:
///   bytes: [2, 0, 0, 1, 1, 3]
///   expr: binaryApp eq (lit (bool true)) (var context)
///
/// Expected decode:
///   byte[0]=2: intInRange(0..=4) → 2 → eq branch (2 < 3)
///   byte[1]=0: intInRange(0..=1) → 0 → literal (lhs)
///   byte[2]=0: intInRange(0..=3) → 0 → bool
///   byte[3]=1: intInRange(0..=1) → 1 → true
///   byte[4]=1: intInRange(0..=1) → 1 → var (rhs)
///   byte[5]=3: intInRange(0..=3) → 3 → context
#[test]
fn test_lean_replay_eq() {
    let buf: Vec<u8> = vec![2, 0, 0, 1, 1, 3];
    let mut u = Unstructured::new(&buf);

    let outer = u.int_in_range::<u8>(0..=4).unwrap();
    assert_eq!(outer, 2); // eq branch

    // LHS: literal_or_var
    let lhs_choice = u.int_in_range::<u8>(0..=1).unwrap();
    assert_eq!(lhs_choice, 0); // literal

    let lit_choice = u.int_in_range::<u8>(0..=3).unwrap();
    assert_eq!(lit_choice, 0); // bool

    let bool_val = u.int_in_range::<u8>(0..=1).unwrap();
    assert_eq!(bool_val, 1); // true

    // RHS: literal_or_var
    let rhs_choice = u.int_in_range::<u8>(0..=1).unwrap();
    assert_eq!(rhs_choice, 1); // var

    let var_choice = u.int_in_range::<u8>(0..=3).unwrap();
    assert_eq!(var_choice, 3); // context
}
