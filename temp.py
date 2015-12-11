class Account:
    """A class computer account. Each account has a two-letter ID
    and the name of the student who is registered to the account.
    """
    num_of_accounts = 0
    def __init__(self, id):
        self.id = id
        Account.num_of_accounts += 1

    def register(self, student):
        self.student = student
        print('Registered!')

    @property
    def type(self):
        return type(self)

