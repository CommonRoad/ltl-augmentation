use ltl_augmentation::formula::parser::ltl_parser;

fn main() {
    let phi = ltl_parser::formula("a -> b U[3, 10] c").expect("Syntax should be correct");
    println!("This is an LTL formula:");
    println!("{}", phi);
}
