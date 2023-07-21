class Logic:
    def __init__(self, name: str, description: str):
        self._name = name
        self._description = description

    def name(self) -> str:
        return self._name

    def description(self) -> str:
        return self._description
