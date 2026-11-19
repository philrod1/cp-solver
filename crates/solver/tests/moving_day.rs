//! Moving day: carry eight pieces of furniture out of a house as quickly as
//! possible, with four people and two trolleys. Two cumulative constraints
//! over the same start times, one for people and one for trolleys, plus a
//! couple of "this before that" orderings.
//!
//! Time is in slots (say, quarter hours). Each item takes some slots, some
//! people and maybe a trolley, all for its whole duration, and no item
//! stops once started. Plans are checked slot by slot by an independent
//! checker.
//!
//! The work comes to 40 person-slots, so on the back of an envelope four
//! people need 10 slots. They need 11: in 10, nobody could ever stand idle,
//! and the orderings make that impossible. The solver can only answer
//! "can it be done by this deadline?", so the best time is shown the same
//! way a puzzle's lack of a solution is: done by 11, impossible by 10.

use solver::{Config, Cumulative, Linear, Model, Outcome, VarId, VarOrder};

struct Item {
    name: &'static str,
    slots: i64,
    people: i64,
    trolleys: i64,
}

const fn item(name: &'static str, slots: i64, people: i64, trolleys: i64) -> Item {
    Item {
        name,
        slots,
        people,
        trolleys,
    }
}

const ITEMS: [Item; 8] = [
    item("piano", 4, 3, 1),
    item("fridge", 2, 2, 1),
    item("double bed", 3, 2, 0),
    item("sofa", 3, 2, 0),
    item("wardrobe", 2, 2, 1),
    item("boxes", 4, 1, 1),
    item("desk", 2, 1, 0),
    item("bookcase", 2, 1, 0),
];

const PIANO: usize = 0;
const SOFA: usize = 3;
const WARDROBE: usize = 4;
const BOXES: usize = 5;

/// `(a, b)`: a must be finished before b starts. The sofa blocks the
/// hallway the piano goes down, and the wardrobe is full of boxes.
const ORDERINGS: [(usize, usize); 2] = [(SOFA, PIANO), (BOXES, WARDROBE)];

#[derive(Clone, Copy)]
struct Crew {
    people: i64,
    trolleys: i64,
}

const CREW: Crew = Crew {
    people: 4,
    trolleys: 2,
};

/// Build the model: `starts[i]` is the slot item i starts in, and every
/// item is done by `deadline`.
fn moving_day(crew: Crew, deadline: i64) -> (Model, Vec<VarId>) {
    let mut model = Model::new();
    let starts: Vec<VarId> = ITEMS
        .iter()
        .map(|it| model.int_var_named(it.name, 0, deadline - it.slots))
        .collect();
    let slots: Vec<i64> = ITEMS.iter().map(|it| it.slots).collect();
    let people: Vec<i64> = ITEMS.iter().map(|it| it.people).collect();
    let trolleys: Vec<i64> = ITEMS.iter().map(|it| it.trolleys).collect();
    model.post(Cumulative::new(&starts, &slots, &people, crew.people));
    model.post(Cumulative::new(&starts, &slots, &trolleys, crew.trolleys));
    for (a, b) in ORDERINGS {
        // starts[a] + slots[a] <= starts[b]
        model.post(Linear::le(&[(starts[a], 1), (starts[b], -1)], -slots[a]));
    }
    (model, starts)
}

/// Is `starts` a plan that finishes by `deadline`, keeps the orderings,
/// and never needs more people or trolleys than `crew` has?
fn is_valid_plan(crew: Crew, deadline: i64, starts: &[i64]) -> bool {
    let running = |i: usize, t: i64| starts[i] <= t && t < starts[i] + ITEMS[i].slots;
    let in_time =
        (0..ITEMS.len()).all(|i| starts[i] >= 0 && starts[i] + ITEMS[i].slots <= deadline);
    let ordered = ORDERINGS
        .iter()
        .all(|&(a, b)| starts[a] + ITEMS[a].slots <= starts[b]);
    let enough = (0..deadline).all(|t| {
        let busy = (0..ITEMS.len()).filter(|&i| running(i, t));
        let (people, trolleys) = busy.fold((0, 0), |(p, r), i| {
            (p + ITEMS[i].people, r + ITEMS[i].trolleys)
        });
        people <= crew.people && trolleys <= crew.trolleys
    });
    in_time && ordered && enough
}

/// The plan as a chart, one row per item, for failure messages:
///
/// ```text
/// piano       ...####....
/// ```
fn gantt(starts: &[i64]) -> String {
    let end = (0..ITEMS.len())
        .map(|i| starts[i] + ITEMS[i].slots)
        .max()
        .unwrap_or(0);
    let mut chart = String::new();
    for (it, &s) in ITEMS.iter().zip(starts) {
        let row: String = (0..end)
            .map(|t| if s <= t && t < s + it.slots { '#' } else { '.' })
            .collect();
        chart.push_str(&format!("{:<12}{row}\n", it.name));
    }
    chart
}

fn plan(crew: Crew, deadline: i64, var_order: VarOrder) -> Option<Vec<i64>> {
    let (model, starts) = moving_day(crew, deadline);
    let config = Config {
        var_order,
        ..Config::default()
    };
    match solver::solve(&model, &config).expect("solver I/O error") {
        Outcome::Satisfiable(sol) => Some(starts.iter().map(|&s| sol.value(s)).collect()),
        Outcome::Unsatisfiable => None,
        Outcome::Unknown => panic!("solver gave up"),
    }
}

// --- The checker itself ------------------------------------------------------

/// A hand-made plan for 11 slots. Of the 44 person-slots, 4 are idle: one
/// person in slots 2 and 6, and two in the last.
///
/// ```text
/// piano       ...####....
/// fridge      .........##
/// double bed  .......###.
/// sofa        ###........
/// wardrobe    .......##..
/// boxes       ####.......
/// desk        ##.........
/// bookcase    ....##.....
/// ```
const BY_HAND: [i64; 8] = [3, 9, 7, 0, 7, 0, 0, 4];

#[test]
fn checker_accepts_a_plan_made_by_hand() {
    assert!(is_valid_plan(CREW, 11, &BY_HAND), "\n{}", gantt(&BY_HAND));
}

#[test]
fn checker_rejects_broken_plans() {
    let broken = |change: fn(&mut [i64; 8])| {
        let mut starts = BY_HAND;
        change(&mut starts);
        starts
    };
    // Each broken plan breaks one rule only, so the crew is unlimited in
    // whatever the rule isn't about.
    let lots_of_people = Crew { people: 99, ..CREW };
    let unlimited = Crew {
        people: 99,
        trolleys: 99,
    };
    let one_trolley = Crew {
        trolleys: 1,
        ..CREW
    };
    // Past the deadline.
    assert!(!is_valid_plan(unlimited, 10, &BY_HAND));
    // The desk alongside the piano and boxes in slot 3: five people.
    assert!(!is_valid_plan(CREW, 11, &broken(|s| s[6] = 3)));
    // The fridge alongside the piano and boxes in slot 3: three trolleys.
    assert!(!is_valid_plan(lots_of_people, 11, &broken(|s| s[1] = 3)));
    // The piano down the hallway before the sofa is out of it.
    assert!(!is_valid_plan(unlimited, 11, &broken(|s| s[SOFA] = 1)));
    // The piano and boxes share slot 3, so one trolley is too few.
    assert!(!is_valid_plan(one_trolley, 11, &BY_HAND));
    // And the same plans are fine when only the rule in question is lifted.
    assert!(is_valid_plan(unlimited, 11, &broken(|s| s[6] = 3)));
    assert!(is_valid_plan(unlimited, 11, &broken(|s| s[1] = 3)));
}

// --- The solver --------------------------------------------------------------

#[test]
fn done_in_eleven_slots() {
    for order in [VarOrder::SmallestDomain, VarOrder::InputOrder] {
        let starts = plan(CREW, 11, order).expect("11 slots is enough");
        assert!(
            is_valid_plan(CREW, 11, &starts),
            "{order:?}: invalid plan\n{}",
            gantt(&starts)
        );
    }
}

#[test]
fn not_in_ten() {
    // 40 person-slots in 10 slots would keep all four people busy in every
    // slot. The piano takes three, so the fourth carries the boxes beside
    // it, and the desk and bookcase must go together beside a two-person
    // job. With the sofa before the piano and the wardrobe after the boxes,
    // the two-person jobs can't be fitted around the piano with nobody
    // left idle.
    for order in [VarOrder::SmallestDomain, VarOrder::InputOrder] {
        assert_eq!(plan(CREW, 10, order), None, "{order:?}");
    }
}

#[test]
fn a_later_deadline_still_gives_valid_plans() {
    for deadline in 12..=16 {
        let starts = plan(CREW, deadline, VarOrder::SmallestDomain).expect("more time is fine");
        assert!(
            is_valid_plan(CREW, deadline, &starts),
            "deadline {deadline}\n{}",
            gantt(&starts)
        );
    }
}

#[test]
fn one_trolley_takes_twelve_slots() {
    // The piano, fridge, wardrobe and boxes need a trolley for 12 slots
    // between them, so with one trolley they can't overlap at all.
    let one_trolley = Crew {
        trolleys: 1,
        ..CREW
    };
    let starts = plan(one_trolley, 12, VarOrder::SmallestDomain).expect("12 slots is enough");
    assert!(
        is_valid_plan(one_trolley, 12, &starts),
        "\n{}",
        gantt(&starts)
    );
    assert_eq!(plan(one_trolley, 11, VarOrder::SmallestDomain), None);
}
