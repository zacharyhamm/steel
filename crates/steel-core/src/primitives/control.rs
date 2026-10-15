use crate::rvals::{Result, SteelVal};
use crate::stop;

pub struct ControlOperations {}
impl ControlOperations {
    pub fn to_string() -> SteelVal {
        SteelVal::FuncV(|args: &[SteelVal]| -> Result<SteelVal> {
            let mut error_message = String::new();

            for arg in args {
                error_message.push(' ');
                match arg {
                    SteelVal::StringV(value) => error_message.push_str(value.as_str()),
                    _ => error_message.push_str(&arg.to_string()),
                }
            }

            Ok(SteelVal::StringV(error_message.into()))
        })
    }

    pub fn error() -> SteelVal {
        SteelVal::FuncV(|args: &[SteelVal]| -> Result<SteelVal> {
            let mut error_message = String::new();

            if !args.is_empty() {
                for arg in args {
                    error_message.push(' ');
                    match arg {
                        SteelVal::StringV(value) => error_message.push_str(value.as_str()),
                        _ => error_message.push_str(&arg.to_string()),
                    }
                }

                stop!(Generic => error_message);
            } else {
                stop!(ArityMismatch => "error takes at least one argument");
            }
        })
    }
}
