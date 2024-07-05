use mltl_simplification::parser::mltl_parser;

fn main() {
    let phi = mltl_parser::formula("a -> b U[3, 10] c").unwrap();
    println!("Hello, world!");
    println!("This is an MLTL formula: {:?}", phi);
}
