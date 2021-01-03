# Chris Culhane 2019
import logging
import re
import shutil
from pathlib import Path

import yaml

logger = logging.getLogger(__name__)


def load_yaml(yamlpath: str):
    """
    Loads a yaml file from a path.
    :param yamlpath: Path to yaml settings file
    :returns: dict settings object """
    yamlpath_full = Path(yamlpath).absolute()

    with open(yamlpath_full, 'r', encoding="utf-8") as stream:
        try:
            outdict = yaml.safe_load(stream)
            return outdict

        except yaml.YAMLError as exc:
            print(exc)
            raise RuntimeError(f"Could not load yaml file at {yamlpath}")


def load_properties(multiline, sep='=', comment_char='#', keys=None):
    """
    Read a multiline string of properties (key/value pair separated by *sep*) into a dict

    :param multiline:    input string of properties
    :param sep:          separator between key and value
    :param comment_char: lines starting with this char are considered comments, not key/value pairs
    :param keys:         list to append the keys to
    :return:
    """
    props = {}
    for line in multiline.splitlines():
        stripped_line = line.strip()
        if stripped_line and not stripped_line.startswith(comment_char):
            key_value = stripped_line.split(sep)
            key = key_value[0].strip()
            value = sep.join(key_value[1:]).strip().strip('"')
            props[key] = value
            if keys != None:
                keys.append(key)
    return props


def copy_logfile(logcopy: logging.Logger, dest_dir, case_code: str = None) -> Path:
    """ Copies the log file from logcopy, to output path pth. Will prefix with case_code if given"""
    Path(dest_dir).mkdir(parents=False, exist_ok=True)

    if case_code is not None:
        new_logname = f"{case_code}_{Path(logcopy.root.handlers[0].baseFilename).name}"
    else:
        new_logname = Path(logcopy.root.handlers[0].baseFilename).name

    copyout = shutil.copy2(logcopy.root.handlers[0].baseFilename, Path(dest_dir, new_logname))
    logcopy.info(f"Copied log file to {copyout}")
    return Path(copyout)


def get_valid_filename(s):
    """
    Return the given string converted to a string that can be used for a clean
    filename. Remove leading and trailing spaces; convert other spaces to
    underscores; and remove anything that is not an alphanumeric, dash,
    underscore, or dot.
    >>> get_valid_filename("john's portrait in 2004.jpg")
    'johns_portrait_in_2004.jpg'
    """
    s = str(s).strip().replace(' ', '_')
    return re.sub(r'(?u)[^-\w.]', '', s)
