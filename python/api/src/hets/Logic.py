class Logic:
    """
    Represents a simplified logic by name and description.
    """
    def __init__(self, name: str, description: str):
        self._name = name
        self._description = description

    def name(self) -> str:
        """
        Returns the name of the logic.
        :return:
        """
        return self._name

    def description(self) -> str:
        """
        Returns the description of the logic.
        :return:
        """
        return self._description
