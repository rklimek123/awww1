from django.core.exceptions import ValidationError


class DigitValidator:
    def validate(self, password, user=None):
        if not any(char.isdigit() for char in password):
            raise ValidationError(
                "This password must contain at least one digit.",
                code='password_no_digit',
            )

    def get_help_text(self):
        return "Your password must contain at least one digit."


class LowerUpperCaseValidator:
    def validate(self, password, user=None):
        if not (any(char.isupper() for char in password) and (any(char.islower() for char in password))):
            raise ValidationError(
                "This password must contain at least one lowercase and one uppercase letter.",
                code='password_no_lowercase_and_uppercase',
            )

    def get_help_text(self):
        return "Your password must contain at least one lowercase and one uppercase letter."


class SymbolValidator:
    def __init__(self, symbols=r"!*_-+={}[]()."):
        self.valid_symbols = symbols

    def validate(self, password, user=None):
        if not (any(char in self.valid_symbols for char in password)):
            raise ValidationError(
                f"This password must contain at least one symbol from the following: {self.valid_symbols}",
                code='password_no_symbol',
                params={'valid_symbols': self.valid_symbols},
            )

    def get_help_text(self):
        return f"Your password must contain at least one symbol from the following: {self.valid_symbols}"
