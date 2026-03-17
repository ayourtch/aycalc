extern crate pest;
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate lazy_static;

use pest::iterators::Pair;
use pest::iterators::Pairs;
use pest::prec_climber::*;
use pest::Parser;
use std::convert::TryInto;
use std::fmt;
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};

#[derive(Debug)]
pub enum Error {
    ParseError(pest::error::Error<Rule>),
    VariableNotFound(String),
    FunctionNotFound(String),
    FunctionCallError(String, String),
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(err: pest::error::Error<Rule>) -> Error {
        Error::ParseError(err)
    }
}

#[derive(Parser)]
#[grammar = "aycalc.pest"]
pub struct AyCalcParser;

/// The type which holds the values the calculator operates on
/// The i128 is chosen because size-wise it is the same as IPv6 address,
/// so this can make certain use cases much simpler. evem if not very elegant.
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum CalcVal {
    Int(i128),
    String(String),
}

impl fmt::Display for CalcVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CalcVal::Int(x) => write!(f, "{}", x),
            CalcVal::String(s) => write!(f, "{}", s),
        }
    }
}

// FIXME: define sensible actions for other type combinations than int,int

impl Add for CalcVal {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 + x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

impl Sub for CalcVal {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 - x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}
impl Mul for CalcVal {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 * x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => {
                match other {
                    CalcVal::Int(x2) => CalcVal::String(s1.repeat(x2.try_into().unwrap_or(1))), // if we could not fit into usize, using 1 seems to be a better option than panic...
                    CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
                }
            }
        }
    }
}
impl Div for CalcVal {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 / x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}
impl Rem for CalcVal {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 % x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

impl Shl for CalcVal {
    type Output = Self;

    fn shl(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 << x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

impl Shr for CalcVal {
    type Output = Self;

    fn shr(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 >> x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

impl BitOr for CalcVal {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 | x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

impl BitAnd for CalcVal {
    type Output = Self;

    fn bitand(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 & x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

impl BitXor for CalcVal {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self {
        match self {
            CalcVal::Int(x1) => match other {
                CalcVal::Int(x2) => CalcVal::Int(x1 ^ x2),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", x1, s2)),
            },
            CalcVal::String(s1) => match other {
                CalcVal::Int(x2) => CalcVal::String(format!("{}{}", s1, x2)),
                CalcVal::String(s2) => CalcVal::String(format!("{}{}", s1, s2)),
            },
        }
    }
}

pub trait GetVar {
    fn get_var_value(&self, varname: &str) -> Result<CalcVal, Error>;
}

pub trait CallFunc {
    fn call_func(&self, funcname: &str, args: &Vec<CalcVal>) -> Result<CalcVal, Error>;
}

lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> = {
        use Assoc::*;
        use Rule::*;

        PrecClimber::new(vec![
            Operator::new(conditional, Left),
            Operator::new(equal, Left)
                | Operator::new(not_equal, Left)
                | Operator::new(greater, Left)
                | Operator::new(greater_equal, Left)
                | Operator::new(less, Left)
                | Operator::new(less_equal, Left),
            Operator::new(bitor, Left) | Operator::new(bitand, Left) | Operator::new(bitxor, Left),
            Operator::new(add, Left) | Operator::new(subtract, Left),
            Operator::new(multiply, Left)
                | Operator::new(divide, Left)
                | Operator::new(modulo, Left)
                | Operator::new(shr, Left)
                | Operator::new(shl, Left),
        ])
    };
}

pub fn parse_calc_val(s: &str) -> Result<CalcVal, Error> {
    if let Ok(x) = s.parse::<i128>() {
        Ok(CalcVal::Int(x))
    } else {
        if s.len() >= 2 {
            if s.starts_with('"') && s.ends_with('"') {
                Ok(CalcVal::String(s[1..s.len() - 1].to_string()))
            } else {
                Ok(CalcVal::String(s.to_string()))
            }
        } else {
            Ok(CalcVal::String(s.to_string()))
        }
    }
}

fn eval_pair(pair: Pair<Rule>, vars: &impl GetVar, func: &impl CallFunc) -> Result<CalcVal, Error> {
    match pair.as_rule() {
        Rule::num => parse_calc_val(pair.as_str()),
        Rule::expr => aycalc_eval(pair.into_inner(), vars, func),
        Rule::conditional => {
            let mut i = pair.into_inner();
            /* the below three unwraps will never panic because the parser verified these three
             * arguments exist */
            let question = i.next().unwrap();
            let true_answer = i.next().unwrap();
            let false_answer = i.next().unwrap();
            if eval_pair(question, vars, func)? == CalcVal::Int(0) {
                eval_pair(false_answer, vars, func)
            } else {
                eval_pair(true_answer, vars, func)
            }
        }
        Rule::string => parse_calc_val(pair.as_str()),
        Rule::variable => {
            // trim is needed because of the bogus space that is returned in case the varname does
            // not contain the dots
            vars.get_var_value(pair.as_str().trim())
        }
        Rule::fncall => {
            let mut inner = pair.into_inner();
            // function name is ensured to exist by parser, so this will never panic
            let function_name = inner.next().unwrap().as_str();
            let mut args: Vec<CalcVal> = vec![];
            for i in inner {
                args.push(eval_pair(i, vars, func)?);
            }
            func.call_func(function_name, &args)
        }
        _ => unreachable!(),
    }
}

fn bool2calcval(b: bool) -> CalcVal {
    if b {
        CalcVal::Int(1)
    } else {
        CalcVal::Int(0)
    }
}

fn aycalc_eval_pure(lhs: CalcVal, op: Pair<Rule>, rhs: CalcVal) -> CalcVal {
    match op.as_rule() {
        Rule::add => lhs + rhs,
        Rule::subtract => lhs - rhs,
        Rule::multiply => lhs * rhs,
        Rule::divide => lhs / rhs,
        Rule::modulo => lhs % rhs,
        Rule::bitand => lhs & rhs,
        Rule::bitor => lhs | rhs,
        Rule::bitxor => lhs ^ rhs,

        Rule::equal => bool2calcval(lhs == rhs),
        Rule::not_equal => bool2calcval(lhs != rhs),
        Rule::greater => bool2calcval(lhs > rhs),
        Rule::greater_equal => bool2calcval(lhs >= rhs),
        Rule::less => bool2calcval(lhs < rhs),
        Rule::less_equal => bool2calcval(lhs <= rhs),
        Rule::shr => lhs >> rhs,
        Rule::shl => lhs << rhs,
        _ => unreachable!(),
    }
}

fn aycalc_eval(
    expression: Pairs<Rule>,
    vars: &impl GetVar,
    func: &impl CallFunc,
) -> Result<CalcVal, Error> {
    PREC_CLIMBER.climb(
        expression,
        |pair: Pair<Rule>| eval_pair(pair, vars, func),
        |lhs: Result<CalcVal, Error>, op: Pair<Rule>, rhs: Result<CalcVal, Error>| {
            let lhs = lhs?;
            let rhs = rhs?;
            Ok(aycalc_eval_pure(lhs, op, rhs))
        },
    )
}

pub fn eval_with(expr: &str, vars: &impl GetVar, func: &impl CallFunc) -> Result<CalcVal, Error> {
    let parser = AyCalcParser::parse(Rule::calculation, expr)?;
    aycalc_eval(parser, vars, func)
}

type EmptyVarsFunc = bool;

impl GetVar for EmptyVarsFunc {
    fn get_var_value(&self, varname: &str) -> Result<CalcVal, Error> {
        Err(Error::VariableNotFound(varname.to_string()))
    }
}

impl CallFunc for EmptyVarsFunc {
    fn call_func(&self, funcname: &str, _args: &Vec<CalcVal>) -> Result<CalcVal, Error> {
        Err(Error::FunctionNotFound(funcname.to_string()))
    }
}

pub fn eval(expr: &str) -> Result<CalcVal, Error> {
    let vf: EmptyVarsFunc = false;
    let parser = AyCalcParser::parse(Rule::calculation, expr)?;
    aycalc_eval(parser, &vf, &vf)
}

#[cfg(test)]
mod tests {
    use crate::*;

    use std::collections::HashMap;

    #[derive(Default)]
    struct MyVarDict {
        vars: HashMap<String, String>,
    }

    impl GetVar for MyVarDict {
        fn get_var_value(&self, varname: &str) -> Result<CalcVal, Error> {
            if let Some(s) = self.vars.get(varname) {
                parse_calc_val(&s)
            } else {
                Err(Error::VariableNotFound(varname.to_string()))
            }
        }
    }

    impl CallFunc for MyVarDict {
        fn call_func(&self, funcname: &str, args: &Vec<CalcVal>) -> Result<CalcVal, Error> {
            println!("Calling func: {} with args: {:?}", &funcname, &args);
            match funcname {
                "int2hex" => match &args[0] {
                    CalcVal::Int(x) => Ok(CalcVal::String(format!("{:x}", x))),
                    z => Err(Error::FunctionCallError(
                        funcname.to_string(),
                        format!("Value {:?} is not an Int", z),
                    )),
                },
                _ => Err(Error::FunctionNotFound(funcname.to_string())),
            }
        }
    }

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn basic_arithmetics() {
        assert_eq!(eval("(2 + 2) * (1 << 4) - 22").unwrap(), CalcVal::Int(42));
    }

    #[test]
    fn concat_int_and_string() {
        assert_eq!(
            eval("2 + \"3\"").unwrap(),
            CalcVal::String("23".to_string())
        );
    }

    #[test]
    fn test_variables() {
        let no_func: EmptyVarsFunc = false;
        let mut vars: MyVarDict = Default::default();
        vars.vars.insert("test".to_string(), "40".to_string());

        assert_eq!(
            eval_with("2 + test", &vars, &no_func).unwrap(),
            CalcVal::Int(42)
        );
    }

    #[test]
    fn test_variables_string() {
        let no_func: EmptyVarsFunc = false;
        let mut vars: MyVarDict = Default::default();
        vars.vars
            .insert("test".to_string(), "testing123".to_string());

        assert_eq!(
            eval_with("test", &vars, &no_func).unwrap(),
            CalcVal::String("testing123".to_string())
        );
    }

    #[test]
    fn test_parse_var_1() {
        assert_eq!(
            parse_calc_val("testing123").unwrap(),
            CalcVal::String("testing123".to_string())
        );
    }

    #[test]
    fn test_parse_var_2() {
        assert_eq!(parse_calc_val("123").unwrap(), CalcVal::Int(123));
    }
    #[test]
    fn test_parse_var_3() {
        assert_eq!(
            parse_calc_val("\"123\"").unwrap(),
            CalcVal::String("123".to_string())
        );
    }

    #[test]
    fn test_functions() {
        let no_vars: EmptyVarsFunc = false;
        let funcs: MyVarDict = Default::default();

        assert_eq!(
            eval_with("int2hex(42)", &no_vars, &funcs).unwrap(),
            CalcVal::String("2a".to_string())
        );
    }

    // --- Arithmetic operators ---

    #[test]
    fn test_addition() {
        assert_eq!(eval("3 + 4").unwrap(), CalcVal::Int(7));
    }

    #[test]
    fn test_subtraction() {
        assert_eq!(eval("10 - 3").unwrap(), CalcVal::Int(7));
    }

    #[test]
    fn test_multiplication() {
        assert_eq!(eval("6 * 7").unwrap(), CalcVal::Int(42));
    }

    #[test]
    fn test_division() {
        assert_eq!(eval("84 / 2").unwrap(), CalcVal::Int(42));
    }

    #[test]
    fn test_modulo() {
        assert_eq!(eval("10 % 3").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_negative_numbers() {
        assert_eq!(eval("-5 + 3").unwrap(), CalcVal::Int(-2));
    }

    // --- Bitwise operators ---

    #[test]
    fn test_bitand() {
        assert_eq!(eval("12 & 10").unwrap(), CalcVal::Int(8));
        assert_eq!(eval("255 & 15").unwrap(), CalcVal::Int(15));
    }

    #[test]
    fn test_bitor() {
        assert_eq!(eval("12 | 10").unwrap(), CalcVal::Int(14));
    }

    #[test]
    fn test_bitxor() {
        assert_eq!(eval("12 ^ 10").unwrap(), CalcVal::Int(6));
    }

    // --- Shift operators ---

    #[test]
    fn test_shl() {
        assert_eq!(eval("1 << 4").unwrap(), CalcVal::Int(16));
    }

    #[test]
    fn test_shr() {
        assert_eq!(eval("16 >> 2").unwrap(), CalcVal::Int(4));
    }

    // --- Comparison operators ---

    #[test]
    fn test_equal_true() {
        assert_eq!(eval("5 == 5").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_equal_false() {
        assert_eq!(eval("5 == 6").unwrap(), CalcVal::Int(0));
    }

    #[test]
    fn test_not_equal_true() {
        assert_eq!(eval("5 != 6").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_not_equal_false() {
        assert_eq!(eval("5 != 5").unwrap(), CalcVal::Int(0));
    }

    #[test]
    fn test_greater_true() {
        assert_eq!(eval("6 > 5").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_greater_false() {
        assert_eq!(eval("5 > 5").unwrap(), CalcVal::Int(0));
    }

    #[test]
    fn test_greater_equal_true() {
        assert_eq!(eval("5 >= 5").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_greater_equal_false() {
        assert_eq!(eval("4 >= 5").unwrap(), CalcVal::Int(0));
    }

    #[test]
    fn test_less_true() {
        assert_eq!(eval("4 < 5").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_less_false() {
        assert_eq!(eval("5 < 5").unwrap(), CalcVal::Int(0));
    }

    #[test]
    fn test_less_equal_true() {
        assert_eq!(eval("5 <= 5").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_less_equal_false() {
        assert_eq!(eval("6 <= 5").unwrap(), CalcVal::Int(0));
    }

    // --- Conditional (ternary) operator ---

    #[test]
    fn test_conditional_true_branch() {
        assert_eq!(eval("1 ? 42 : 0").unwrap(), CalcVal::Int(42));
    }

    #[test]
    fn test_conditional_false_branch() {
        assert_eq!(eval("0 ? 42 : 99").unwrap(), CalcVal::Int(99));
    }

    // --- Operator precedence ---

    #[test]
    fn test_precedence_mul_over_add() {
        assert_eq!(eval("2 + 3 * 4").unwrap(), CalcVal::Int(14));
    }

    #[test]
    fn test_precedence_parentheses() {
        assert_eq!(eval("(2 + 3) * 4").unwrap(), CalcVal::Int(20));
    }

    #[test]
    fn test_precedence_shift_same_as_mul() {
        // shifts are at the same precedence as multiply/divide/modulo
        // 2 * 3 << 1: with equal precedence and left assoc, this is (2 * 3) << 1 = 12
        assert_eq!(eval("2 * 3 << 1").unwrap(), CalcVal::Int(12));
    }

    #[test]
    fn test_precedence_comparison_below_add() {
        // 3 + 1 > 3 should be (3 + 1) > 3 = 1
        assert_eq!(eval("3 + 1 > 3").unwrap(), CalcVal::Int(1));
    }

    #[test]
    fn test_precedence_bitwise_between_add_and_comparison() {
        // 2 | 1 + 3: add binds tighter, so 2 | 4 = 6
        assert_eq!(eval("2 | 1 + 3").unwrap(), CalcVal::Int(6));
    }

    // --- String operations ---

    #[test]
    fn test_string_repeat() {
        assert_eq!(
            eval("\"ab\" * 3").unwrap(),
            CalcVal::String("ababab".to_string())
        );
    }

    #[test]
    fn test_string_concat_two_strings() {
        assert_eq!(
            eval("\"hello\" + \"world\"").unwrap(),
            CalcVal::String("helloworld".to_string())
        );
    }

    #[test]
    fn test_string_equality() {
        assert_eq!(eval("\"abc\" == \"abc\"").unwrap(), CalcVal::Int(1));
        assert_eq!(eval("\"abc\" == \"def\"").unwrap(), CalcVal::Int(0));
    }

    // --- Variables with dots ---

    #[test]
    fn test_dotted_variable() {
        let no_func: EmptyVarsFunc = false;
        let mut vars: MyVarDict = Default::default();
        vars.vars.insert("foo.bar".to_string(), "10".to_string());

        assert_eq!(
            eval_with("foo.bar + 5", &vars, &no_func).unwrap(),
            CalcVal::Int(15)
        );
    }

    // --- Functions with multiple args ---

    #[test]
    fn test_function_with_expression_arg() {
        let no_vars: EmptyVarsFunc = false;
        let funcs: MyVarDict = Default::default();

        assert_eq!(
            eval_with("int2hex(16 + 26)", &no_vars, &funcs).unwrap(),
            CalcVal::String("2a".to_string())
        );
    }

    // --- Complex expressions ---

    #[test]
    fn test_nested_parentheses() {
        assert_eq!(eval("((2 + 3) * (4 - 1))").unwrap(), CalcVal::Int(15));
    }

    #[test]
    fn test_chained_comparisons() {
        // (1 == 1) == 1 => 1 == 1 => 1 (left associative)
        assert_eq!(eval("1 == 1 == 1").unwrap(), CalcVal::Int(1));
    }

    // --- CalcVal Display trait ---

    #[test]
    fn test_display_int() {
        let v = CalcVal::Int(42);
        assert_eq!(format!("{}", v), "42");
    }

    #[test]
    fn test_display_string() {
        let v = CalcVal::String("hello".to_string());
        assert_eq!(format!("{}", v), "hello");
    }

    // --- String operand branches for Add ---

    #[test]
    fn test_add_string_plus_int() {
        assert_eq!(
            eval("\"hello\" + 5").unwrap(),
            CalcVal::String("hello5".to_string())
        );
    }

    // --- String operand branches for Sub ---

    #[test]
    fn test_sub_int_minus_string() {
        assert_eq!(
            eval("5 - \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_sub_string_minus_int() {
        assert_eq!(
            eval("\"a\" - 1").unwrap(),
            CalcVal::String("a1".to_string())
        );
    }

    #[test]
    fn test_sub_string_minus_string() {
        assert_eq!(
            eval("\"a\" - \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for Mul ---

    #[test]
    fn test_mul_int_times_string() {
        assert_eq!(
            eval("3 * \"x\"").unwrap(),
            CalcVal::String("3x".to_string())
        );
    }

    #[test]
    fn test_mul_string_times_string() {
        assert_eq!(
            eval("\"a\" * \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for Div ---

    #[test]
    fn test_div_int_div_string() {
        assert_eq!(
            eval("5 / \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_div_string_div_int() {
        assert_eq!(
            eval("\"a\" / 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_div_string_div_string() {
        assert_eq!(
            eval("\"a\" / \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for Rem ---

    #[test]
    fn test_rem_int_mod_string() {
        assert_eq!(
            eval("5 % \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_rem_string_mod_int() {
        assert_eq!(
            eval("\"a\" % 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_rem_string_mod_string() {
        assert_eq!(
            eval("\"a\" % \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for Shl ---

    #[test]
    fn test_shl_int_string() {
        assert_eq!(
            eval("5 << \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_shl_string_int() {
        assert_eq!(
            eval("\"a\" << 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_shl_string_string() {
        assert_eq!(
            eval("\"a\" << \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for Shr ---

    #[test]
    fn test_shr_int_string() {
        assert_eq!(
            eval("5 >> \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_shr_string_int() {
        assert_eq!(
            eval("\"a\" >> 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_shr_string_string() {
        assert_eq!(
            eval("\"a\" >> \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for BitOr ---

    #[test]
    fn test_bitor_int_string() {
        assert_eq!(
            eval("5 | \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_bitor_string_int() {
        assert_eq!(
            eval("\"a\" | 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_bitor_string_string() {
        assert_eq!(
            eval("\"a\" | \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for BitAnd ---

    #[test]
    fn test_bitand_int_string() {
        assert_eq!(
            eval("5 & \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_bitand_string_int() {
        assert_eq!(
            eval("\"a\" & 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_bitand_string_string() {
        assert_eq!(
            eval("\"a\" & \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- String operand branches for BitXor ---

    #[test]
    fn test_bitxor_int_string() {
        assert_eq!(
            eval("5 ^ \"x\"").unwrap(),
            CalcVal::String("5x".to_string())
        );
    }

    #[test]
    fn test_bitxor_string_int() {
        assert_eq!(
            eval("\"a\" ^ 2").unwrap(),
            CalcVal::String("a2".to_string())
        );
    }

    #[test]
    fn test_bitxor_string_string() {
        assert_eq!(
            eval("\"a\" ^ \"b\"").unwrap(),
            CalcVal::String("ab".to_string())
        );
    }

    // --- parse_calc_val edge cases ---

    #[test]
    fn test_parse_calc_val_single_char() {
        // Single char string (len < 2) goes through the else branch
        assert_eq!(
            parse_calc_val("x").unwrap(),
            CalcVal::String("x".to_string())
        );
    }

    // --- Error paths ---

    #[test]
    fn test_parse_error() {
        // Invalid expression triggers ParseError via From impl
        let result = eval("+++");
        assert!(result.is_err());
        match result.unwrap_err() {
            Error::ParseError(_) => {}
            e => panic!("Expected ParseError, got {:?}", e),
        }
    }

    #[test]
    fn test_variable_not_found() {
        // eval() uses EmptyVarsFunc which returns VariableNotFound
        let result = eval("somevar + 1");
        assert!(result.is_err());
        match result.unwrap_err() {
            Error::VariableNotFound(name) => assert_eq!(name, "somevar"),
            e => panic!("Expected VariableNotFound, got {:?}", e),
        }
    }

    #[test]
    fn test_function_not_found() {
        // eval() uses EmptyVarsFunc which returns FunctionNotFound
        let result = eval("somefunc(1)");
        assert!(result.is_err());
        match result.unwrap_err() {
            Error::FunctionNotFound(name) => assert_eq!(name, "somefunc"),
            e => panic!("Expected FunctionNotFound, got {:?}", e),
        }
    }
}
