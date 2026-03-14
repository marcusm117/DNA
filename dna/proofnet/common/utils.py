import os
import os.path as osp
import regex as re
from typing import Union, Tuple, List, Dict, Any, Optional, Generator, AsyncGenerator, Set
import asyncio
import signal

import pexpect

from .constants import ident_pattern
from .dataclasses import Environment


class Spwan(pexpect.spawn):
    async def send_async(self, s):
        if self.delaybeforesend is not None:
            await asyncio.sleep(self.delaybeforesend)

        s = self._coerce_send_string(s)
        self._log(s, 'send')

        b = self._encoder.encode(s, final=False)

        return os.write(self.child_fd, b)        
        # while b:
        #     try:
        #         bytes_written = os.write(self.child_fd, b)
        #         b = b[bytes_written:]
        #     except BlockingIOError:
        #         await asyncio.sleep(0)
        #         pass
        
        # return bytes_written  

    async def sendline_async(self, s=''):
        '''Wraps send(), sending string ``s`` to child process, with
        ``os.linesep`` automatically appended. Returns number of bytes
        written.  Only a limited number of bytes may be sent for each
        line in the default terminal mode, see docstring of :meth:`send`.
        '''
        s = self._coerce_send_string(s)
        return await self.send_async(s + self.linesep)

    async def read_async(self, size=-1):
        '''This reads at most "size" bytes from the file (less if the read hits
        EOF before obtaining size bytes). If the size argument is negative or
        omitted, read all data until EOF is reached. The bytes are returned as
        a string object. An empty string is returned when EOF is encountered
        immediately. '''

        if size == 0:
            return self.string_type()
        if size < 0:
            # delimiter default is EOF
            await self.expect(self.delimiter, async_=True)
            return self.before

        # I could have done this more directly by not using expect(), but
        # I deliberately decided to couple read() to expect() so that
        # I would catch any bugs early and ensure consistent behavior.
        # It's a little less efficient, but there is less for me to
        # worry about if I have to later modify read() or expect().
        # Note, it's OK if size==-1 in the regex. That just means it
        # will never match anything in which case we stop only on EOF.
        cre = re.compile(self._coerce_expect_string('.{%d}' % size), re.DOTALL)
        # delimiter default is EOF
        index = await self.expect([cre, self.delimiter], async_=True)
        if index == 0:
            ### FIXME self.before should be ''. Should I assert this?
            return self.after
        return self.before

    async def readline_async(self, size=-1):
        '''This reads and returns one entire line. The newline at the end of
        line is returned as part of the string, unless the file ends without a
        newline. An empty string is returned if EOF is encountered immediately.
        This looks for a newline as a CR/LF pair (\\r\\n) even on UNIX because
        this is what the pseudotty device returns. So contrary to what you may
        expect you will receive newlines as \\r\\n.

        If the size argument is 0 then an empty string is returned. In all
        other cases the size argument is ignored, which is not standard
        behavior for a file-like object. '''

        if size == 0:
            return self.string_type()
        # delimiter default is EOF
        index = await self.expect([self.crlf, self.delimiter], async_=True)
        if index == 0:
            return self.before + self.crlf
        else:
            return self.before

    async def terminate_async(self, force=False):
        '''This forces a child process to terminate. It starts nicely with
        SIGHUP and SIGINT. If "force" is True then moves onto SIGKILL. This
        returns True if the child was terminated. This returns False if the
        child could not be terminated. '''

        if not self.isalive():
            return True
        try:
            self.kill(signal.SIGHUP)
            await asyncio.sleep(self.delayafterterminate)
            if not self.isalive():
                return True
            self.kill(signal.SIGCONT)
            await asyncio.sleep(self.delayafterterminate)
            if not self.isalive():
                return True
            self.kill(signal.SIGINT)
            await asyncio.sleep(self.delayafterterminate)
            if not self.isalive():
                return True
            if force:
                self.kill(signal.SIGKILL)
                await asyncio.sleep(self.delayafterterminate)
                if not self.isalive():
                    return True
                else:
                    return False
            return False
        except OSError:
            # I think there are kernel timing issues that sometimes cause
            # this to happen. I think isalive() reports True, but the
            # process is dead to the kernel.
            # Make one last attempt to see if the kernel is up to date.
            await asyncio.sleep(self.delayafterterminate)
            if not self.isalive():
                return True
            else:
                return False

def format_doc_both(p: Dict) -> str:
    return f'''Formal Declaration: {p['header'].replace('🔗<|PREMISE|>🔗', '')[:1536]}
Informal Explanation: {p['informalization'][:1536]}'''

def format_doc_only_if(p: Dict) -> str:
    return f'''Informal Explanation: {p['informalization'][:1536]}'''

def format_doc_only_f(p: Dict) -> str:
    return f'''Formal Declaration: {p['header'].replace('🔗<|PREMISE|>🔗', '')[:1536]}'''

def replace_span(span: Tuple[int, int], replacement: str, input_string: str) -> str:
    start, end = span
    return input_string[:start] + replacement + input_string[end:]

def post_process_statement(stmt: str, init_env: Environment, repl: 'REPL', full_name_to_id: Dict[str, int], opens: Optional[str]=None) -> Tuple[str, Set[int]]:
    load_env = repl.run_cmd(
        (
            (opens or '') + '\n' + \
            'set_option pp.fullNames true\n' + \
            stmt
        ),
        #* By `set_option pp.fullNames true`, we can parse full names of formal statements from their proof states.
        init_env)
    assert isinstance(load_env, Environment) and not [m for m in load_env.messages if m.severity == 'error']
    init_state = load_env.sorries[0]

    context_vars: Set[str] = set()
    parsed_dependencies: Set[int] = set()

    telescopes, goal = init_state.goal.split('⊢ ')

    for l in telescopes.splitlines() + [goal]:
        if ':' in l:
            split_pos = l.find(':')
            var_names, var_type = l[:split_pos].split(), l[split_pos+1:]
            context_vars.update(var_names)
        else:
            var_type = l

        matches = list(ident_pattern.finditer(var_type))
        for i in range(len(matches)-1):
            assert matches[i].span()[0] < matches[i].span()[1] and matches[i].span()[1] <= matches[i+1].span()[0]

        for match in reversed(matches):
            if match.group() in context_vars:
                continue
            elif match.group() in full_name_to_id.keys():
                parsed_dependencies.add(full_name_to_id[match.group()])

    parsed_statement = 'example ' + '\n'.join(['(' + l + ')' for l in telescopes.splitlines()]) + '\n: ' + goal + '\n:= by sorry'
    post_env = repl.run_cmd(parsed_statement, init_env)
    assert isinstance(post_env, Environment) and not [m for m in post_env.messages if m.severity == 'error']
    assert post_env.sorries[0].goal == init_state.goal

    return parsed_statement, parsed_dependencies
