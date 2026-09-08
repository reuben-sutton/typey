//! Compact lookup data derived from owned CFGs.
//!
//! The index is deliberately syntax-only.  It lets inference answer which
//! owned operation or conditional covers a source span without retaining the
//! full graph in every analyzer, and it keeps CFG discovery out of the type
//! evaluator.

use super::{Cfg, Conditional};
use crate::hir::{BodyId, Program};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Default)]
pub struct CfgIndex {
    body_count: usize,
    unsupported_count: usize,
    call_spans: HashSet<(usize, usize)>,
    write_spans: HashSet<(usize, usize)>,
    conditionals: HashMap<(usize, usize), Conditional>,
}

impl CfgIndex {
    #[must_use]
    pub fn from_program(program: &Program) -> Self {
        let mut index = Self {
            body_count: program.bodies.len(),
            ..Self::default()
        };
        for (body, _) in program.bodies.iter().enumerate() {
            let graph = super::lower::build_for_index(program, BodyId(body as u32));
            index.add_graph(program, &graph);
        }
        index
    }

    #[must_use]
    pub fn from_graphs(program: &Program, graphs: &[Cfg]) -> Self {
        let mut index = Self {
            body_count: graphs.len(),
            ..Self::default()
        };
        for graph in graphs {
            index.add_graph(program, graph);
        }
        index
    }

    fn add_graph(&mut self, program: &Program, graph: &Cfg) {
        self.unsupported_count += graph.unsupported_spans.len();
        for conditional in &graph.conditionals {
            if let Some(expression) = program.expression(conditional.expression) {
                self.conditionals.insert(
                    (expression.span.start as usize, expression.span.end as usize),
                    conditional.clone(),
                );
            }
        }
        for block in &graph.blocks {
            for operation in &block.operations {
                let span = (operation.span.start as usize, operation.span.end as usize);
                match &operation.kind {
                    super::OperationKind::Call { .. } => {
                        self.call_spans.insert(span);
                    }
                    super::OperationKind::Write { .. } => {
                        self.write_spans.insert(span);
                    }
                    _ => {}
                }
            }
        }
    }

    #[must_use]
    pub fn body_count(&self) -> usize {
        self.body_count
    }

    #[must_use]
    pub fn unsupported_count(&self) -> usize {
        self.unsupported_count
    }

    #[must_use]
    pub fn has_call(&self, span: (usize, usize)) -> bool {
        self.call_spans.contains(&span)
    }

    #[must_use]
    pub fn has_write(&self, span: (usize, usize)) -> bool {
        self.write_spans.contains(&span)
    }

    #[must_use]
    pub fn conditional(&self, span: (usize, usize)) -> Option<&Conditional> {
        self.conditionals.get(&span)
    }
}
