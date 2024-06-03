use std::io;

use clap::{self, Parser, Subcommand};
use mdbook::preprocess::{CmdPreprocessor, Preprocessor};

use mdbook_trpl_note::TrplNote;

fn main() -> Result<(), String> {
    let cli = Cli::parse();
    let simple_note = TrplNote;
    if let Some(Command::Supports { renderer }) = cli.command {
        return if simple_note.supports_renderer(&renderer) {
            Ok(())
        } else {
            Err(format!("Renderer '{renderer}' is unsupported"))
        };
    }

    let (ctx, book) = CmdPreprocessor::parse_input(io::stdin())
        .map_err(|e| format!("Error preprocessing Markdown: {e}"))?;
    let processed = simple_note.run(&ctx, book).map_err(|e| format!("{e}"))?;
    serde_json::to_writer(io::stdout(), &processed).map_err(|e| format!("{e}"))
}

/// A simple preprocessor for semantic notes in The Rust Programming Language
/// book.
///
/// Note: This is not yet intended for general usage, as the format it uses for
/// callouts/admonitions is wholly specific to the way the Rust book uses those,
/// and totally incompatible with e.g. GitHub-Flavored Markdown’s admonitions.
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
    /// All renderers are supported! This is the contract for mdBook.
    Supports { renderer: String },
}
