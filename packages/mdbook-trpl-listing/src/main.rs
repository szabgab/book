use std::io;

use clap::{self, Parser, Subcommand};
use mdbook::preprocess::{CmdPreprocessor, Preprocessor};

use mdbook_trpl_listing::TrplListing;

fn main() -> Result<(), String> {
    let cli = Cli::parse();
    if let Some(Command::Supports { renderer }) = cli.command {
        return if TrplListing.supports_renderer(&renderer) {
            Ok(())
        } else {
            Err(format!("Renderer '{renderer}' is unsupported"))
        };
    }

    let (ctx, book) = CmdPreprocessor::parse_input(io::stdin())
        .map_err(|e| format!("{e}"))?;
    let processed = TrplListing.run(&ctx, book).map_err(|e| format!("{e}"))?;
    serde_json::to_writer(io::stdout(), &processed).map_err(|e| format!("{e}"))
}

/// A simple preprocessor for semantic markup for code listings in The Rust
/// Programming Language book.
///
/// Note: This is not yet intended for general usage, although the idea it
/// implements may at some point be upstreamed into mdBook proper, since its
/// output is more accessible and friendlier to styling nicely than the baseline
/// output from mdBook.
///
/// It supports the two basic modes of all mdbook preprocessors:
///
/// • Checking renderer support, e.g. `mdbook-trpl-listing supports html`.
///
/// • Accepting input from `stdin` when invoked by mdbook itself as part of
///   preprocessing a book.
#[derive(Parser, Debug)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Is the renderer supported?
    ///
    /// At present only the `html` and `markdown` renderers are supported, since
    /// this works by replacing specific Markdown contracts with HTML directly
    /// in the Markdown source before running mdBook on it.
    Supports {
        /// The name of an mdBook renderer to check. A list of renderers can be
        /// found at https://rust-lang.github.io/mdBook/format/configuration/renderers.html
        renderer: String,
    },
}
