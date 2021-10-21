use aycalc::*;

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

fn main() {
    let mut vars: MyVarDict = Default::default(); // HashMap<String, String> = HashMap::new();
    vars.vars.insert("test".into(), "1".into());
    vars.vars.insert("multiplier".into(), "20".into());
    let expr = std::env::args().nth(1).unwrap();
    println!("Parse result: {:?}", eval_with(&expr, &vars, &vars));
}
