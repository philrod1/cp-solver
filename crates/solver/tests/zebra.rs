//! The Zebra puzzle (Life International, 1962), also called Einstein's riddle.
//!
//! Five houses in a row, each with a colour, an owner's nationality, a drink,
//! a brand of cigarette and a pet. Fourteen clues; who drinks water, and who
//! owns the zebra?
//!
//! Model: one variable per attribute value, holding the number (1..=5) of the
//! house it belongs to. Each category is an all-different. "Same house" is a
//! linear equality, "immediately right of" is a linear equality with an
//! offset, and "next to" is a table of the eight neighbouring pairs.
//!
//! The answer is checked by testing every clue directly against the
//! solution, not by trusting the model.

use solver::{
    AllDifferent, Cell, Config, Linear, Model, NotEqual, Outcome, Solution, Table, VarId,
};

/// Attribute value names in each category, in a fixed order.
const COLOURS: [&str; 5] = ["red", "green", "ivory", "yellow", "blue"];
const NATIONS: [&str; 5] = ["english", "spanish", "ukrainian", "norwegian", "japanese"];
const DRINKS: [&str; 5] = ["coffee", "tea", "milk", "orange_juice", "water"];
const SMOKES: [&str; 5] = [
    "old_gold",
    "kools",
    "chesterfield",
    "lucky_strike",
    "parliament",
];
const PETS: [&str; 5] = ["dog", "snails", "fox", "horse", "zebra"];

struct Zebra {
    model: Model,
    /// Every attribute value, with the variable holding its house number.
    all: Vec<(&'static str, VarId)>,
}

impl Zebra {
    fn var(&self, name: &str) -> VarId {
        self.all
            .iter()
            .find(|(n, _)| *n == name)
            .unwrap_or_else(|| panic!("no {name}"))
            .1
    }

    /// Clue: `a` and `b` are in the same house.
    fn same(&mut self, a: &str, b: &str) {
        let (a, b) = (self.var(a), self.var(b));
        self.model.post(Linear::eq(&[(a, 1), (b, -1)], 0));
    }

    /// Clue: `a` is in the house immediately to the right of `b`.
    fn right_of(&mut self, a: &str, b: &str) {
        let (a, b) = (self.var(a), self.var(b));
        self.model.post(Linear::eq(&[(a, 1), (b, -1)], 1));
    }

    /// Clue: `a` is in the house next to `b`, on either side. The table
    /// lists every pair of neighbouring houses.
    fn next_to(&mut self, a: &str, b: &str) {
        let (a, b) = (self.var(a), self.var(b));
        let neighbours: Vec<Vec<Cell>> = (1..5)
            .flat_map(|h| {
                [
                    vec![h.into(), (h + 1).into()],
                    vec![(h + 1).into(), h.into()],
                ]
            })
            .collect();
        self.model.post(Table::new(&[a, b], &neighbours));
    }

    /// Clue: `a` is in house number `house`.
    fn in_house(&mut self, a: &str, house: i64) {
        let a = self.var(a);
        self.model.post(Linear::eq(&[(a, 1)], house));
    }
}

fn puzzle() -> Zebra {
    let mut model = Model::new();
    let mut all = Vec::new();
    for category in [COLOURS, NATIONS, DRINKS, SMOKES, PETS] {
        let vars: Vec<VarId> = category.iter().map(|_| model.int_var(1, 5)).collect();
        model.post(AllDifferent::new(&vars));
        all.extend(category.iter().copied().zip(vars));
    }
    let mut z = Zebra { model, all };

    z.same("english", "red"); //               2. The Englishman lives in the red house.
    z.same("spanish", "dog"); //               3. The Spaniard owns the dog.
    z.same("coffee", "green"); //              4. Coffee is drunk in the green house.
    z.same("ukrainian", "tea"); //             5. The Ukrainian drinks tea.
    z.right_of("green", "ivory"); //           6. Green is immediately right of ivory.
    z.same("old_gold", "snails"); //           7. The Old Gold smoker owns snails.
    z.same("kools", "yellow"); //              8. Kools are smoked in the yellow house.
    z.in_house("milk", 3); //                  9. Milk is drunk in the middle house.
    z.in_house("norwegian", 1); //            10. The Norwegian lives in the first house.
    z.next_to("chesterfield", "fox"); //      11. Chesterfields are smoked next to the fox.
    z.next_to("kools", "horse"); //           12. Kools are smoked next to the horse.
    z.same("lucky_strike", "orange_juice"); // 13. The Lucky Strike smoker drinks orange juice.
    z.same("japanese", "parliament"); //      14. The Japanese smokes Parliaments.
    z.next_to("norwegian", "blue"); //        15. The Norwegian lives next to the blue house.
    z
}

fn solve(z: &Zebra) -> Option<Solution> {
    match solver::solve(&z.model, &Config::default()).expect("solver I/O error") {
        Outcome::Satisfiable(sol) => Some(sol),
        Outcome::Unsatisfiable => None,
        Outcome::Unknown => panic!("solver gave up"),
    }
}

/// Check every clue against a solution, independently of the model.
fn obeys_every_clue(z: &Zebra, sol: &Solution) -> bool {
    let house = |name: &str| sol.value(z.var(name));
    let same = |a, b| house(a) == house(b);
    let next_to = |a, b| (house(a) - house(b)).abs() == 1;
    let categories_ok = [COLOURS, NATIONS, DRINKS, SMOKES, PETS].iter().all(|cat| {
        let mut hs: Vec<i64> = cat.iter().map(|n| house(n)).collect();
        hs.sort_unstable();
        hs == [1, 2, 3, 4, 5]
    });
    categories_ok
        && same("english", "red")
        && same("spanish", "dog")
        && same("coffee", "green")
        && same("ukrainian", "tea")
        && house("green") == house("ivory") + 1
        && same("old_gold", "snails")
        && same("kools", "yellow")
        && house("milk") == 3
        && house("norwegian") == 1
        && next_to("chesterfield", "fox")
        && next_to("kools", "horse")
        && same("lucky_strike", "orange_juice")
        && same("japanese", "parliament")
        && next_to("norwegian", "blue")
}

#[test]
fn the_norwegian_drinks_water_and_the_japanese_owns_the_zebra() {
    let z = puzzle();
    let sol = solve(&z).expect("the puzzle has a solution");
    assert!(obeys_every_clue(&z, &sol), "the solution breaks a clue");

    let owner_of = |thing: &str| {
        let h = sol.value(z.var(thing));
        NATIONS
            .iter()
            .find(|n| sol.value(z.var(n)) == h)
            .copied()
            .unwrap()
    };
    assert_eq!(owner_of("water"), "norwegian");
    assert_eq!(owner_of("zebra"), "japanese");
}

#[test]
fn the_whole_street_matches_the_known_answer() {
    let z = puzzle();
    let sol = solve(&z).expect("the puzzle has a solution");
    let street: Vec<Vec<&str>> = (1..=5)
        .map(|h| {
            z.all
                .iter()
                .filter(|(_, v)| sol.value(*v) == h)
                .map(|(name, _)| *name)
                .collect()
        })
        .collect();
    assert_eq!(
        street,
        [
            ["yellow", "norwegian", "water", "kools", "fox"],
            ["blue", "ukrainian", "tea", "chesterfield", "horse"],
            ["red", "english", "milk", "old_gold", "snails"],
            ["ivory", "spanish", "orange_juice", "lucky_strike", "dog"],
            ["green", "japanese", "coffee", "parliament", "zebra"],
        ]
    );
}

#[test]
fn the_answers_are_forced() {
    // With either answer ruled out, no street satisfies every clue, so the
    // clues really do determine who owns the zebra and who drinks water.
    let mut z = puzzle();
    let (zebra, japanese) = (z.var("zebra"), z.var("japanese"));
    z.model.post(NotEqual::new(zebra, japanese));
    assert!(solve(&z).is_none(), "someone else could own the zebra");

    let mut z = puzzle();
    let (water, norwegian) = (z.var("water"), z.var("norwegian"));
    z.model.post(NotEqual::new(water, norwegian));
    assert!(solve(&z).is_none(), "someone else could drink water");
}
