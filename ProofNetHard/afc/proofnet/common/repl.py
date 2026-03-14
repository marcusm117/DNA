import json
import asyncio
from pathlib import Path
from typing import Union, Tuple, List, Dict, Any, Optional, Generator

import pexpect
import dacite
from loguru import logger

from .constants import REPL_TIMEOUT
from .dataclasses import LeanError, Message, Environment, ProofState
from .utils import Spwan


class REPL:
    def __init__(
            self,
            repl_root: Optional[Path] = None,
            project_root: Optional[Path] = None,
            timeout: Optional[int]=REPL_TIMEOUT,
            dacite_config: Optional[dacite.Config] = None
    ) -> None:
        # When the keyword argument timeout is -1 (default),
        # then TIMEOUT will raise after the default value specified by the class timeout attribute.
        # When None, TIMEOUT will not be raised and may block indefinitely until match.
        self.repl_root = repl_root
        self.project_root = project_root
        self.timeout = timeout
        self.dacite_config = dacite.Config(
            check_types=True,
            strict=True,
            strict_unions_match=True
        ) if dacite_config is None else dacite_config
        self.lock = asyncio.Lock()

    def _run_interactive(self):
        # Suppress verbose REPL debug logs in normal runs
        if self.repl_root is None:
            assert self.project_root is None, '`project_root` must be None if `repl_root` is None'
            self.proc = Spwan(
                f'lake exe repl',
                timeout=self.timeout,
                encoding="utf-8"
            )
        else:
            self.proc = Spwan(
                f'lake env {self.repl_root}/.lake/build/bin/repl',
                cwd=self.project_root,
                timeout=self.timeout,
                encoding="utf-8"
            )
        # Disable pexpect debug echoing by default
        self.proc.debug = False

    def _close(self):
        self.proc.close()
        if self.proc.isalive():
            self.proc.terminate(force=True)

    def __enter__(self) -> "REPL":
        self._run_interactive()

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        self._close()

    def __del__(self):
        del self.repl_root
        del self.project_root
        del self.timeout
        if hasattr(self, "proc"):
            self._close()
            del self.proc

    def _submit_request(self, req: str) -> str:
        """Submit a request to Lean and get the response.
        """
        logger.trace(f"Request: {req}, executing...")
        self.proc.sendline(req)
        self.proc.expect_exact(req + "\r\n", timeout=self.timeout)

        self.proc.sendline()
        self.proc.expect_exact("\r\n", timeout=self.timeout)
        try:
            index = self.proc.expect('\}\r\n', timeout=self.timeout)
            output = self.proc.before + self.proc.match.group()
            logger.trace(f"Output: {output}")
            return output
        except pexpect.exceptions.TIMEOUT:
            logger.error(f'Request "{req}" failed: timeout')
            return json.dumps({'message': f'Request "{req}" failed: timeout'})

    def run_cmd(self, command: str, env: Optional[Environment] = None) -> Union[Environment, LeanError]:
        output = self._submit_request(json.dumps(
            {"cmd": command, "env": env.env} if env is not None else {"cmd": command},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        try:
            return dacite.from_dict(
                data_class=Environment,
                data=data,
                config=self.dacite_config
            )
        except dacite.exceptions.UnexpectedDataError as e:
            return dacite.from_dict(
                data_class=LeanError,
                data=data,
                config=self.dacite_config
            )

    def run_file(self, path: Path, return_all_states: bool = False) -> Union[Environment, LeanError]:
        output = self._submit_request(json.dumps(
            {"path": path, "allTactics": return_all_states},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        try:
            return dacite.from_dict(
                data_class=Environment,
                data=data,
                config=self.dacite_config
            )
        except dacite.exceptions.UnexpectedDataError as e:
            return dacite.from_dict(
                data_class=LeanError,
                data=data,
                config=self.dacite_config
            )

    def run_tac(self, tactic: str, state: ProofState) -> Union[ProofState, LeanError]:
        output = self._submit_request(json.dumps(
            {"tactic": tactic, "proofState": state.proofState},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        try:
            return dacite.from_dict(
                data_class=ProofState,
                data=data,
                config=self.dacite_config
            )
        except dacite.exceptions.UnexpectedDataError as e:
            return dacite.from_dict(
                data_class=LeanError,
                data=data,
                config=self.dacite_config
            )

    def pickle_env(self, path: Path, env: Environment) -> Union[Environment, LeanError]:
        output = self._submit_request(json.dumps(
            {"pickleTo": path, "env": env.env},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=Environment,
            data=data,
            config=self.dacite_config
        )

    def unpickle_env(self, path: Path) -> Union[Environment, LeanError]:
        output = self._submit_request(json.dumps(
            {"unpickleEnvFrom": path},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=Environment,
            data=data,
            config=self.dacite_config
        )

    def pickle_state(self, path: Path, state: ProofState) -> Union[ProofState, LeanError]:
        output = self._submit_request(json.dumps(
            {"pickleTo": path, "proofState": state.proofState},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=ProofState,
            data=data,
            config=self.dacite_config
        )

    def unpickle_state(self, path: Path) -> Union[ProofState, LeanError]:
        logger.trace(f"unpickle path : {path}")
        output = self._submit_request(json.dumps(
            {"unpickleProofStateFrom": path},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=ProofState,
            data=data,
            config=self.dacite_config
        )

    # Async version of the following actions.
    async def _submit_request_async(self, req: str) -> str:
        """Submit a request to Lean and get the response.
        """
        logger.trace(f"Async request: {req}, acquiring lock...")

        # async with self.lock:
        await self.lock.acquire()
        try:
            logger.trace(f"Async request: {req}, executing...")
            await self.proc.sendline_async(req)
            await self.proc.expect_exact(req + "\r\n", timeout=self.timeout, async_=True)

            await self.proc.sendline_async()
            await self.proc.expect_exact("\r\n", timeout=self.timeout, async_=True)
            try:
                index = await self.proc.expect('\}\r\n', timeout=self.timeout, async_=True)
                output = self.proc.before + self.proc.match.group()
                # logger.trace(f"Async output: {output}")
                logger.trace(f"Async output: {output}")
                return output
            except pexpect.exceptions.TIMEOUT:
                logger.error(f'Async request "{req}" failed: timeout')
                return json.dumps({'message': f'Request "{req}" failed: timeout'})
        finally:
            self.lock.release()
            logger.trace(f"Async lock released.")

    async def run_cmd_async(self, command: str, env: Optional[Environment] = None) -> Union[Environment, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"cmd": command, "env": env.env} if env is not None else {"cmd": command},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        try:
            return dacite.from_dict(
                data_class=Environment,
                data=data,
                config=self.dacite_config
            )
        except dacite.exceptions.UnexpectedDataError as e:
            return dacite.from_dict(
                data_class=LeanError,
                data=data,
                config=self.dacite_config
            )

    async def run_file_async(self, path: Path, return_all_states: bool = False) -> Union[Environment, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"path": path, "allTactics": return_all_states},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        try:
            return dacite.from_dict(
                data_class=Environment,
                data=data,
                config=self.dacite_config
            )
        except dacite.exceptions.UnexpectedDataError as e:
            logger.error(f'dacite.exceptions.UnexpectedDataError: {e}')
            return dacite.from_dict(
                data_class=LeanError,
                data=data,
                config=self.dacite_config
            )

    async def run_tac_async(self, tactic: str, state: ProofState) -> Union[ProofState, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"tactic": tactic, "proofState": state.proofState},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        try:
            return dacite.from_dict(
                data_class=ProofState,
                data=data,
                config=self.dacite_config
            )
        except dacite.exceptions.UnexpectedDataError as e:
            return dacite.from_dict(
                data_class=LeanError,
                data=data,
                config=self.dacite_config
            )

    async def pickle_env_async(self, path: Path, env: Environment) -> Union[Environment, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"pickleTo": path, "env": env.env},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=Environment,
            data=data,
            config=self.dacite_config
        )

    async def unpickle_env_async(self, path: Path) -> Union[Environment, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"unpickleEnvFrom": path},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=Environment,
            data=data,
            config=self.dacite_config
        )

    async def pickle_state_async(self, path: Path, state: ProofState) -> Union[ProofState, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"pickleTo": path, "proofState": state.proofState},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=ProofState,
            data=data,
            config=self.dacite_config
        )

    async def unpickle_state_async(self, path: Path) -> Union[ProofState, LeanError]:
        output = await self._submit_request_async(json.dumps(
            {"unpickleProofStateFrom": path},
            ensure_ascii=False
        ))
        try:
            data = json.loads(output)
        except json.decoder.JSONDecodeError as e:
            logger.error(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
            return LeanError(f'json.decoder.JSONDecodeError: {e} when decoding {[output]}')
        return dacite.from_dict(
            data_class=ProofState,
            data=data,
            config=self.dacite_config
        )
