use lazy_static::lazy_static;
use log::{Level, LevelFilter, MetadataBuilder, Record};
use env_logger::{Builder, Logger, WriteStyle};
use fern::colors::{Color, ColoredLevelConfig};
use chrono::{Datelike, Local, Timelike};

use std::{fmt, io::Write};

lazy_static! {
    pub static ref RAP_LOGGER: Logger = {
        let color_line = ColoredLevelConfig::new()
            .info(Color::White)
            .error(Color::Red)
            .warn(Color::Yellow)
            .debug(Color::White)
            .trace(Color::BrightBlack);

        let color_level = color_line.info(Color::Green);

        let builder = Builder::new()
            .format(move |buf, record| {
                let time_now = Local::now();
                writeln!(
                    buf,
                    "{}{}-{}:{}:{}:{} |BACK| |{:5}{}| [{}] {}\x1B[0m",
                    format_args!(
                        "\x1B[{}m",
                        color_line.get_color(&record.level()).to_fg_str()
                    ),
                    time_now.month(),
                    time_now.day(),
                    time_now.hour(),
                    time_now.minute(),
                    time_now.second(),
                    color_level.color(record.level()),
                    format_args!(
                        "\x1B[{}m",
                        color_line.get_color(&record.level()).to_fg_str()
                    ),
                    record.target(),
                    record.args()
                )
            })
            .filter(None, LevelFilter::Info)
            .write_style(WriteStyle::Always)
            .build()
        ;
        builder
    };
}

#[derive(Debug, Copy, Clone, Hash)]
pub enum RapLogLevel {
    Info,
    Debug,
    Trace,
    Error,
    Warn,
}

pub fn record_msg(args: fmt::Arguments<'_>, level: RapLogLevel) -> Record<'_> {
    let meta = MetadataBuilder::new()
        .target("RAP")
        .level(
            match level {
                RapLogLevel::Info => Level::Info,
                RapLogLevel::Debug => Level::Debug,
                RapLogLevel::Trace => Level::Trace,
                RapLogLevel::Error => Level::Error,
                RapLogLevel::Warn => Level::Warn,
            }
        )
        .build();

    let record = Record::builder()
        .metadata(meta)
        .args(args.clone())
        .build();

    record
}

#[macro_export]
macro_rules! rap_info {
    ($($arg:tt)+) => (
        RAP_LOGGER.log(&record_msg(format_args!($($arg)+), RapLogLevel::Info))
    );
}

#[macro_export]
macro_rules! rap_error {
    ($($arg:tt)+) => (
        RAP_LOGGER.log(&record_msg(format_args!($($arg)+), RapLogLevel::Error))
    );
}

#[macro_export]
macro_rules! rap_warn {
    ($($arg:tt)+) => (
        RAP_LOGGER.log(&record_msg(format_args!($($arg)+), RapLogLevel::Warn))
    );
}