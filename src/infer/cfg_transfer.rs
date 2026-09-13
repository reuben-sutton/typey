use super::{Analyzer, CallArguments, Environment, OwnedCallInput};
use crate::hir;
use crate::types::Type;

mod arguments;
mod assignment;
mod body;
mod builtins;
mod calls;
mod collections;
mod construction;
mod context;
mod dispatch;
mod exceptions;
mod flow;
mod globals;
mod intrinsics;
mod outcomes;
mod patterns;
mod preflight;
mod value;

impl<'src> Analyzer<'src> {
    pub(super) fn cfg_body_preflight_failure(
        &self,
        body_id: hir::BodyId,
    ) -> Option<(hir::Span, String)> {
        if let Some(failure) = self.cfg_preflight_failures.get(&body_id) {
            return failure.clone();
        }
        preflight::body_transfer_failure_ignoring_ranges(
            &self.program.hir_program,
            body_id,
            &self.rbi_ranges,
        )
        .map(|failure| (failure.span, failure.reason))
    }

    pub(super) fn transfer_owned_symbol_call(
        &mut self,
        input: &OwnedCallInput,
        receiver: &Type,
        arguments: &CallArguments<'_>,
        environment: &mut Environment,
    ) -> Result<Type, String> {
        if let Type::Union(members) = receiver {
            let initial_environment = environment.clone();
            let mut result_type = Type::Never;
            let mut joined_environment: Option<Environment> = None;
            for member in members {
                let mut member_environment = initial_environment.clone();
                let result = dispatch::transfer_receiver_call(
                    self,
                    input,
                    member,
                    arguments,
                    &[],
                    &mut member_environment,
                    None,
                )?;
                if result.missing_method {
                    self.report_missing_method_component_if_needed_at(
                        input.site,
                        member,
                        input.name.as_str(),
                        receiver,
                    );
                }
                result_type = result_type.join(&result.type_);
                joined_environment = Some(match joined_environment {
                    Some(joined) => joined.join(&member_environment),
                    None => member_environment,
                });
            }
            if let Some(joined_environment) = joined_environment {
                *environment = joined_environment;
            }
            return Ok(result_type);
        }
        let result = dispatch::transfer_receiver_call(
            self,
            input,
            receiver,
            arguments,
            &[],
            environment,
            None,
        )?;
        if result.missing_method {
            self.report_missing_method_if_needed_at(
                input.site,
                receiver,
                input.name.as_str(),
                false,
            );
        }
        Ok(result.type_)
    }
}

#[cfg(test)]
mod tests {
    use super::super::cfg_state::BlockState;
    use super::super::{Environment, Flow, FlowKind};
    use crate::types::Type;

    fn environment(name: &str, type_: Type) -> Environment {
        let mut environment = Environment::default();
        environment.bind(name, type_);
        environment
    }

    #[test]
    fn normal_path_wins_over_an_abrupt_path() {
        let normal = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let returned = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::abrupt(FlowKind::Return),
        );

        let joined = normal.join(&returned);

        assert_eq!(joined.environment.get("value"), Type::String);
        assert_eq!(
            joined.values.as_slice(),
            &[Some(Type::String.join(&Type::Integer))]
        );
        assert!(joined.flow.contains(FlowKind::Normal));
        assert!(joined.flow.contains(FlowKind::Return));
    }

    #[test]
    fn two_normal_paths_join_values_and_environment_facts() {
        let left = BlockState::with_values(
            environment("value", Type::String),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(
            environment("value", Type::Integer),
            vec![Some(Type::Integer)],
            Flow::normal(),
        );

        let joined = left.join(&right);

        let expected = Type::String.join(&Type::Integer);
        assert_eq!(joined.environment.get("value"), expected);
        assert_eq!(joined.values.as_slice(), &[Some(expected)]);
    }

    #[test]
    fn missing_value_on_one_edge_is_not_invented_at_the_join() {
        let left = BlockState::with_values(
            Environment::default(),
            vec![Some(Type::String)],
            Flow::normal(),
        );
        let right = BlockState::with_values(Environment::default(), vec![None], Flow::normal());

        assert_eq!(left.join(&right).values.as_slice(), &[None]);
    }
}
