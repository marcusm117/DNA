from dataclasses import dataclass, field
from typing import Union, Tuple, List, Dict, Any, Optional, Generator, Set, Callable
import json
import regex as re

import networkx as nx
from loguru import logger

from .constants import TERMINAL_TEXT


@dataclass(unsafe_hash=True)
class Pos:
    line: int
    column: int
    def __eq__(self, other) -> bool:
        return isinstance(other, Pos) and all([
            self.line == other.line,
            self.column == other.column,
        ])
    def __le__(self, other):
        if self.line < other.line:
            return True
        if self.line == other.line:
            return self.column <= other.column
        return False
    def __lt__(self, other):
        if self.line < other.line:
            return True
        if self.line == other.line:
            return self.column < other.column
        return False
    def __str__(self) -> str:
        return f'({self.line}, {self.column})'


@dataclass(frozen=True)
class Sorry:
    pos: Pos
    endPos: Pos
    goal: str
    proofState: int

    def serialize(self) -> Dict[str, Any]:
        return {
            'pos': str(self.pos),
            'endPos': str(self.endPos),
            'goal': self.goal,
            'proofState': self.proofState
        }

@dataclass(frozen=True)
class LeanError:
    message: str

    def __str__(self) -> str:
        return self.message

    def serialize(self) -> Dict[str, Any]:
        return {
            'message': self.message,
        }

@dataclass(frozen=True)
class Message:
    severity: str
    data: str
    pos: Pos
    endPos: Optional[Pos]=None

    def serialize(self) -> Dict[str, Any]:
        return {
            'severity': self.severity,
            'pos': str(self.pos),
            'endPos': str(self.endPos),
            'data': self.data
        }


@dataclass(frozen=True)
class Environment:
    env: int
    sorries: List[Sorry] = field(default_factory=list) 
    messages: List[Message] = field(default_factory=list) 

    def serialize(self) -> Dict[str, Any]:
        return {
            'env': self.env,
            'sorries': [s.serialize() for s in self.sorries],
            'messages': [m.serialize() for m in self.messages],
        }

@dataclass(frozen=True)
class ProofState:
    proofState: int
    goals: List[str]
    sorries: List[Sorry] = field(default_factory=list) 
    messages: List[Message] = field(default_factory=list) 

    def __str__(self) -> str:
        return '\n\n'.join(self.goals) if len(self.goals) > 0 else TERMINAL_TEXT

    def __le__(self, other: 'ProofState'):
        return str(self) <= str(other)

    def __lt__(self, other: 'ProofState'):
        return str(self) < str(other)

    def __eq__(self, other: 'ProofState'):
        return isinstance(other, ProofState) and all([
            self.proofState == other.proofState,
            self.goals == other.goals,
            self.sorries == other.sorries,
            self.messages == other.messages,
        ])

    def content_eq(self, other: 'ProofState'):
        return isinstance(other, ProofState) and all([
            self.goals == other.goals,
            self.sorries == other.sorries,
            [m for m in self.messages if m.severity == 'error'] == [m for m in other.messages if m.severity == 'error'],
        ])
    
    def serialize(self) -> Dict[str, Any]:
        return {
            'proofState': self.proofState,
            'goals': self.goals,
            'sorries': [s.serialize() for s in self.sorries],
            'messages': [m.serialize() for m in self.messages],
        }
