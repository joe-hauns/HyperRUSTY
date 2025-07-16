use ir::*;






struct loopcondition {
    model1, env
    model2, env
    symstates1, vec<states>
    symstates2, vec<states>
}

impl loopcondition {
    new()

    legal_state(self) {
        valid_states = vec();
        for symstate in symstates1 {
            valid_states.push(model1.generate_scope_constraints_for_state(symstate))
        }

        Bool::and(ctx, &valid_states)
    }
}