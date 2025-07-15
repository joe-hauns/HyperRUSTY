use colored::*;
use std::process::exit;
fn apply_level(string: &str, level: i8) -> ColoredString {
    match level {
        1 => ("completion: ".to_owned() + string).bright_green(),
        2 => ("info: ".to_owned() + string).bright_cyan(),
        3 => ("warning: ".to_owned() + string).bright_yellow(),
        4 => ("error: ".to_owned() + string).bright_red(),
        5 => ("fatal error: ".to_owned() + string).red().bold(),
        _ => string.red().bold().italic(),

    }
}

/// Raises an error and exits the program
/// level 1: completion
/// level 2: info
/// level 3: warning
/// level 4: error
/// level 5: fatal error
///
/// # Arguments
///
/// * `error` - A string slice that holds the error message
/// * `level` - The error level, higher means more severe
pub fn raise_error(error: &str, level: i8) {
    eprintln!("{}", apply_level(&error, level));
    if level>3 {
        exit(1);
    }
}