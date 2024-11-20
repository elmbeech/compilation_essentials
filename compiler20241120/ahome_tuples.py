            
    ############################################################################
    # Assign Homes
    ############################################################################
              
    def collect_locals_arg(self, a: arg) -> Set[location]:
        match a:
            case Global(name):
                return set()
            case _:
                return super().collect_locals_arg(a)

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Global(name):
                return Global(name)
            case _:
                return super().assign_homes_arg(a, home)

