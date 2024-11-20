    ###########################################################################
    # Uncover Live
    ###########################################################################

    def vars_arg(self, a: arg) -> Set[location]:
        match a:
            case Global(name):
                return set()
            case _:
                return super().vars_arg(a)

