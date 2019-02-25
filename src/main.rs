use std::env;
use std::path::PathBuf;
use std::io::{Cursor, Write};
use ykpack::{DefId, Decoder, Pack, Mir, BasicBlock, Terminator, BasicBlockIndex, CallOperand};
use fallible_iterator::FallibleIterator;
use elf;
use tempfile;
use std::process::Command;
use std::collections::HashMap;

fn write_edge_raw(w: &mut Write, src_node: &str , dest_node: &str, edge_label: Option<&str>) {
    if let Some(el) = edge_label {
        writeln!(w, "\"{}\" -> \"{}\" [label = \"{}\"];", src_node.to_string(), dest_node.to_string(), el.to_string()).unwrap();
    } else {
        writeln!(w, "\"{}\" -> \"{}\";", src_node.to_string(), dest_node.to_string()).unwrap();
    }
}

fn write_edge(w: &mut Write, src_node: BasicBlockIndex, dest_node: BasicBlockIndex, edge_label: Option<&str>) {
    write_edge_raw(w, &src_node.to_string(), &dest_node.to_string(), edge_label);
}

fn def_id_node_prefix(d: &DefId) -> String {
    format!("{}-{}", d.crate_hash, d.def_idx)
}

fn style_node(w: &mut dyn Write, node_name: &str, label: Option<&str>, attrs: Option<&str>) {
    let mut s = format!("\"{}\"", (node_name));
    let label = label.unwrap_or(node_name);

    s.push_str(&format!("[ label = \"{}\"", label));
    if let Some(a) = attrs {
        s.push_str(&format!(", {}", a));
    }
    s.push(']');
    writeln!(w, "\t{}", s).unwrap();
}

fn get_statements_text(blk: &BasicBlock) -> String {
    let mut lines = Vec::new();
    for stmt in &blk.stmts {
        lines.push(format!("{:?}", stmt));
    }

    lines.join("\\n")
}

fn write_edges(_mir: &Mir, cx: &mut Context, src_bb: BasicBlockIndex, block: &BasicBlock, fh: &mut dyn Write) {
    let goto_label = String::from("goto");
    let ret_label = String::from("ret");
    let call_label = String::from("call");
    let cleanup_label = String::from("cleanup");
    let abort_label = String::from("abort");
    let false_edge_label = String::from("false edge");
    let false_unwind_label = String::from("false unwind");
    let switch_int_label = String::from("switch_int");
    let resume_label = String::from("resume");
    let unreach_label = String::from("unreachable");
    let gen_drop_label = String::from("gen drop");
    let drop_label = String::from("drop");
    let unwind_label = String::from("unwind");
    let drop_replace_label = String::from("drop+replace");
    let yield_label = String::from("yield");
    let assert_label = String::from("assert");

    let src_bb_str = src_bb.to_string();

    let term_label = match block.term {
        Terminator::Goto{ target_bb } => {
            write_edge(fh, src_bb, target_bb, None);
            &goto_label
        },
        Terminator::FalseEdges { real_target_bb } => {
            write_edge(fh, src_bb, real_target_bb, None);
            &false_edge_label
        },
        Terminator::FalseUnwind { real_target_bb } => {
            write_edge(fh, src_bb, real_target_bb, None);
            &false_unwind_label
        },
        Terminator::SwitchInt{ ref target_bbs } => {
            for target_bb in target_bbs.clone() {
                write_edge(fh, src_bb, target_bb, None);
            }
            &switch_int_label
        },
        Terminator::Resume => {
            let resume_node = cx.external_node_label(resume_label.clone());
            style_node(fh, &resume_node, None, Some("shape=point, color=blue"));
            write_edge_raw(fh, &src_bb_str, &resume_node, None);
            &resume_label
        },
        Terminator::Abort => {
            let abort_node = cx.external_node_label(abort_label.clone());
            style_node(fh, &abort_node, None, Some("shape=point, color=red"));
            write_edge_raw(fh, &src_bb_str, &abort_node, None);
            &abort_label
        },
        Terminator::Return => {
            let ret_node = cx.external_node_label(ret_label.clone());
            style_node(fh, &ret_node, None, Some("shape=point"));
            write_edge_raw(fh, &src_bb_str, &ret_node, None);
            &ret_label
        },
        Terminator::Unreachable => {
            let unreach_node = cx.external_node_label(unreach_label.clone());
            style_node(fh, &unreach_node, None, None);
            write_edge_raw(fh, &src_bb_str, &unreach_node, None);
            &unreach_label
        },
        Terminator::GeneratorDrop => {
            let gen_drop_node = cx.external_node_label(gen_drop_label.clone());
            style_node(fh, &gen_drop_node, None, None);
            write_edge_raw(fh, &src_bb_str, &gen_drop_node, None);
            &gen_drop_label
        }
        Terminator::Drop { target_bb, unwind_bb } => {
            write_edge(fh, src_bb, target_bb, None);
            if let Some(u_bb) = unwind_bb {
                write_edge(fh, src_bb, u_bb, Some(&unwind_label));
            }
            &drop_label
        },
        Terminator::DropAndReplace { target_bb, unwind_bb } => {
            write_edge(fh, src_bb, target_bb, None);
            if let Some(u_bb) = unwind_bb {
                write_edge(fh, src_bb, u_bb, Some(&unwind_label));
            }
            &drop_replace_label
        },
        Terminator::Assert { target_bb, cleanup_bb } => {
            write_edge(fh, src_bb, target_bb, None);
            if let Some(c_bb) = cleanup_bb {
                write_edge(fh, src_bb, c_bb, Some(&unwind_label));
            }
            &assert_label
        },
        Terminator::Yield { resume_bb: target_bb, drop_bb: except_bb } => {
            write_edge(fh, src_bb, target_bb, None);
            if let Some(e_bb) = except_bb {
                write_edge(fh, src_bb, e_bb, Some(&drop_label));
            }
            &yield_label
        },
        Terminator::Call { ref operand, ref cleanup_bb, ref ret_bb } => {
            let target_node_str = match operand {
                CallOperand::Fn(def_id) => cx.external_node_label(def_id_node_prefix(def_id)),
                _ => cx.external_node_label(String::from("???")),
            };
            style_node(fh, &target_node_str, None, Some("fillcolor = lightblue1, style = filled"));

            write_edge_raw(fh, &src_bb_str, &target_node_str, None);
            if let Some(c_bb) = cleanup_bb {
                write_edge(fh, src_bb, *c_bb, Some(&cleanup_label));
            }
            if let Some(r_bb) = ret_bb {
                write_edge_raw(fh, &target_node_str, &r_bb.to_string(), None);
            }
            &call_label
        },
    };

    let stmts_str = get_statements_text(block);

    style_node(fh, &src_bb_str, Some(&format!("{{{} | {} | {}}}", src_bb_str, stmts_str, term_label)), Some("shape = record, style=filled, fillcolor=beige"));
}

struct Context {
    external_nodes: HashMap<String, usize>,
}

impl Context {
    fn new() -> Self {
        Self { external_nodes: HashMap::new() }
    }

    fn external_node_label(&mut self, node_prefix: String) -> String {
        let count = self.external_nodes.entry(node_prefix.clone()).or_default();
        let label = format!("{}({})", node_prefix, count);
        *count += 1;
        label
    }
}

fn graph(mir: Mir) {
    let mut fh = tempfile::Builder::new()
        .prefix(&format!("mir-{}-{}", mir.def_id.crate_hash, mir.def_id.def_idx))
        .rand_bytes(0)
        .tempfile_in("mirs")
        .unwrap();

    writeln!(fh, "digraph \"g\" {{").unwrap();
    writeln!(fh, "\tnode [ shape=box ]").unwrap(); // Default node style.
    style_node(&mut fh, "__entry", Some(""), Some("shape=point")); // Entry node.
    write_edge_raw(&mut fh, &"__entry", &"0", None);

    let mut ctxt = Context::new();

    for (bb_idx, bb_data) in mir.blocks.iter().enumerate() {
        write_edges(&mir, &mut ctxt, bb_idx as u32, &bb_data, &mut fh);
    }

    writeln!(fh, "}}").unwrap();

    let output_arg = format!("-o{}.png", fh.path().to_str().unwrap());
    let mut cmd = Command::new("dot");
    cmd.arg("-Tpng")
        .arg(&output_arg)
        .arg(fh.path());

    cmd.status().expect("dot failed");

    // Persist the dot file for debugging.
    let persist_path = format!("{}.dot.txt", fh.path().to_str().unwrap());
    fh.persist(persist_path).unwrap();
}

fn process(path: PathBuf) {
    let ef = elf::File::open_path(&path).unwrap();
    let sec = ef.get_section(".yk_mir_cfg").unwrap();
    let mut curs = Cursor::new(&sec.data);
    let mut dec = Decoder::from(&mut curs);

    while let Some(pack) = dec.next().unwrap() {
        let Pack::Mir(mir) = pack;
        println!("{:?}", mir.def_id);
        graph(mir);
    }
}

fn main() {
    let mut args = env::args().skip(1);
    let bin = args.next().unwrap();
    process(PathBuf::from(bin));
}
