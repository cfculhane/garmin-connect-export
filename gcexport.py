#!/usr/bin/python
# -*- coding: utf-8 -*-

"""
File: gcexport.py
Original author: Kyle Krafka (https://github.com/kjkjava/)
Date: April 28, 2015
Fork author: Michael P (https://github.com/moderation/)
Date: February 21, 2016

Description:    Use this script to export your fitness data from Garmin Connect.
                See README.md for more information.

Activity & event types:
    https://connect.garmin.com/modern/main/js/properties/event_types/event_types.properties
    https://connect.garmin.com/modern/main/js/properties/activity_types/activity_types.properties
"""


import argparse
import csv
import json
import logging
import pickle
import re
import string
import sys
import unicodedata
import zipfile
from datetime import datetime, timedelta, tzinfo
from getpass import getpass
from math import floor
from os import stat, utime
from os.path import dirname, join, realpath
from pathlib import Path
from typing import Dict, Union

import requests
from pprintpp import pprint
from tqdm import tqdm

from shared_logging import setup_logging
from utilities import load_yaml, load_properties, get_valid_filename

logging.getLogger("urllib3").setLevel(logging.WARNING)
logging.getLogger("requests").setLevel(logging.WARNING)

__version__ = '3.0.0'

# this is almost the datetime format Garmin used in the activity-search-service
# JSON 'display' fields (Garmin didn't zero-pad the date and the hour, but %d and %H do)
ALMOST_RFC_1123 = "%a, %d %b %Y %H:%M"

# used by sanitize_filename()
VALID_FILENAME_CHARS = "-_.() %s%s" % (string.ascii_letters, string.digits)

# map the numeric parentTypeId to its name for the CSV output
PARENT_TYPE_ID = {
    1: 'running',
    2: 'cycling',
    3: 'hiking',
    4: 'other',
    9: 'walking',
    17: 'any',
    26: 'swimming',
    29: 'fitness_equipment',
    71: 'motorcycling',
    83: 'transition',
    144: 'diving',
    149: 'yoga'
}

# typeId values using pace instead of speed
USES_PACE = {1, 3, 9}  # running, hiking, walking

# Maximum number of activities you can request at once.
# Used to be 100 and enforced by Garmin for older endpoints; for the current endpoint 'LIST'
# the limit is not known (I have less than 1000 activities and could get them all in one go)
LIMIT_MAXIMUM = 1000

MAX_TRIES = 3

CSV_TEMPLATE = join(dirname(realpath(__file__)), "csv_header_default.yaml")

WEBHOST = "https://connect.garmin.com"
REDIRECT = "https://connect.garmin.com/modern/"
BASE_URL = "https://connect.garmin.com/en-US/signin"
SSO = "https://sso.garmin.com/sso"
CSS = "https://static.garmincdn.com/com.garmin.connect/ui/css/gauth-custom-v1.2-min.css"

LOGIN_PARAMS = {
    'service': REDIRECT,
    'webhost': WEBHOST,
    'source': BASE_URL,
    'redirectAfterAccountLoginUrl': REDIRECT,
    'redirectAfterAccountCreationUrl': REDIRECT,
    'gauthHost': SSO,
    'locale': 'en_US',
    'id': 'gauth-widget',
    'cssUrl': CSS,
    'clientId': 'GarminConnect',
    'rememberMeShown': 'true',
    'rememberMeChecked': 'false',
    'createAccountShown': 'true',
    'openCreateAccount': 'false',
    'displayNameShown': 'false',
    'consumeServiceTicket': 'false',
    'initialFocus': 'true',
    'embedWidget': 'false',
    'generateExtraServiceTicket': 'true',
    'generateTwoExtraServiceTickets': 'false',
    'generateNoServiceTicket': 'false',
    'globalOptInShown': 'true',
    'globalOptInChecked': 'false',
    'mobile': 'false',
    'connectLegalTerms': 'true',
    'locationPromptShown': 'true',
    'showPassword': 'true'
}


def resolve_path(directory, subdir, time):
    """
    Replace time variables and returns changed path. Supported place holders are {YYYY} and {MM}
    :param directory: export root directory
    :param subdir: subdirectory, can have place holders.
    :param time: date-time-string
    :return: Updated dictionary string
    """
    ret = join(directory, subdir)
    if re.compile(".*{YYYY}.*").match(ret):
        ret = ret.replace("{YYYY}", time[0:4])
    if re.compile(".*{MM}.*").match(ret):
        ret = ret.replace("{MM}", time[5:7])

    return ret


def hhmmss_from_seconds(sec):
    """Helper function that converts seconds to HH:MM:SS time format."""
    if isinstance(sec, (float, int)):
        formatted_time = str(timedelta(seconds=int(sec))).zfill(8)
    else:
        formatted_time = "0.000"
    return formatted_time


def kmh_from_mps(mps):
    """Helper function that converts meters per second (mps) to km/h."""
    return str(mps * 3.6)


def sanitize_filename(name, max_length=0):
    """
    Remove or replace characters that are unsafe for filename
    """
    # inspired by https://stackoverflow.com/a/698714/3686
    cleaned_filename = unicodedata.normalize('NFKD', name).encode('ASCII', 'ignore') if name else ''
    stripped_filename = ''.join(c for c in cleaned_filename if c in VALID_FILENAME_CHARS).replace(' ', '_')
    return stripped_filename[:max_length] if max_length > 0 else stripped_filename


def write_to_file(filename, content, mode, file_time=None):
    """Helper function that persists content to file."""
    with open(filename, mode) as f:
        f.write(content)
    if file_time:
        utime(filename, (file_time, file_time))


def absent_or_null(element, act):
    """Return False only if act[element] is valid and not None"""
    if not act:
        return True
    elif element not in act:
        return True
    elif act[element]:
        return False
    return True


def from_activities_or_detail(element, act, detail, detail_container):
    """Return detail[detail_container][element] if valid and act[element] (or None) otherwise"""
    if absent_or_null(detail_container, detail) or absent_or_null(element, detail[detail_container]):
        return None if absent_or_null(element, act) else act[element]
    return detail[detail_container][element]


def trunc6(some_float):
    """Return the given float as string formatted with six digit precision"""
    return "{0:12.6f}".format(floor(some_float * 1000000) / 1000000).lstrip()


# A class building tzinfo objects for fixed-offset time zones.
# (copied from https://docs.python.org/2/library/datetime.html)
class FixedOffset(tzinfo):
    """Fixed offset in minutes east from UTC."""

    def __init__(self, offset, name):
        super(FixedOffset, self).__init__()
        self.__offset = timedelta(minutes=offset)
        self.__name = name

    def utcoffset(self, dt):
        del dt  # unused
        return self.__offset

    def tzname(self, dt):
        del dt  # unused
        return self.__name

    def dst(self, dt):
        del dt  # unused
        return timedelta(0)


def offset_date_time(time_local, time_gmt):
    """
    Build an 'aware' datetime from two 'naive' datetime objects (that is timestamps
    as present in the activitylist-service.json), using the time difference as offset.
    """
    local_dt = datetime.strptime(time_local, "%Y-%m-%d %H:%M:%S")
    gmt_dt = datetime.strptime(time_gmt, "%Y-%m-%d %H:%M:%S")
    offset = local_dt - gmt_dt
    offset_tz = FixedOffset(offset.seconds / 60, "LCL")
    return local_dt.replace(tzinfo=offset_tz)


def pace_or_speed_raw(type_id, parent_type_id, mps):
    """Convert speed (m/s) to speed (km/h) or pace (min/km) depending on type and parent type"""
    kmh = 3.6 * mps
    if (type_id in USES_PACE) or (parent_type_id in USES_PACE):
        return 60 / kmh
    return kmh


def pace_or_speed_formatted(type_id, parent_type_id, mps):
    """
    Convert speed (m/s) to string: speed (km/h as x.x) or
    pace (min/km as MM:SS), depending on type and parent type
    """
    kmh = 3.6 * mps
    if (type_id in USES_PACE) or (parent_type_id in USES_PACE):
        # format seconds per kilometer as MM:SS, see https://stackoverflow.com/a/27751293
        return '{0:02d}:{1:02d}'.format(*divmod(int(round(3600 / kmh)), 60))
    return "{0:.1f}".format(round(kmh, 1))


class CsvFilter(object):
    """Collects, filters and writes CSV."""

    def __init__(self, csv_file, csv_header_properties):
        self.__csv_file = csv_file
        with open(csv_header_properties, 'r') as prop:
            csv_header_props = prop.read()
        self.__csv_columns = []
        self.__csv_headers = load_properties(csv_header_props, keys=self.__csv_columns)
        self.__csv_field_names = []
        for column in self.__csv_columns:
            self.__csv_field_names.append(self.__csv_headers[column])
        self.__writer = csv.DictWriter(self.__csv_file, fieldnames=self.__csv_field_names, quoting=csv.QUOTE_ALL)
        self.__current_row = {}

    def write_header(self):
        """Write the active column names as CSV header"""
        self.__writer.writeheader()

    def write_row(self):
        """Write the prepared CSV record"""
        self.__writer.writerow(self.__current_row)
        self.__current_row = {}

    def set_column(self, name, value):
        """
        Store a column value (if the column is active) into
        the record prepared for the next write_row call
        """
        if value and name in self.__csv_columns:
            # must encode in UTF-8 because the Python 'csv' module doesn't support unicode
            self.__current_row[self.__csv_headers[name]] = value.encode('utf8')

    def is_column_active(self, name):
        """Return True if the column is present in the header template"""
        return name in self.__csv_columns


def parse_arguments() -> Dict:
    """
    Setup the argument parser and parse the command line arguments.
    """
    current_date = datetime.now().strftime('%Y-%m-%d')
    activities_directory = Path(__path__).parent.joinpath(current_date + '_garmin_connect_export')

    parser = argparse.ArgumentParser(description='Garmin Connect Exporter')

    parser.add_argument('--version', action='version', version='%(prog)s ' + __version__,
                        help='print version and exit')
    parser.add_argument('-v', '--verbosity', action='count',
                        help='increase output verbosity')
    parser.add_argument('--username',
                        help='your Garmin Connect username or email address (otherwise, you will be prompted)')
    parser.add_argument('--password',
                        help='your Garmin Connect password (otherwise, you will be prompted)')
    parser.add_argument('-c', '--count', default='1',
                        help="number of recent activities to download, or 'all' or 'new' (default: 1), "
                             "'new' or 'number' downloads the latest activities by activity's date/time")
    parser.add_argument('-e', '--external',
                        help='path to external program to pass CSV file too')
    parser.add_argument('-a', '--external_args',
                        help='additional arguments to pass to external program')
    parser.add_argument('-f', '--format', choices=['gpx', 'tcx', 'original', 'json'], default='gpx',
                        help="export format; can be 'gpx', 'tcx', 'original' or 'json' (default: 'gpx')")
    parser.add_argument('-d', '--directory', default=activities_directory,
                        help='the directory to export to (default: \'./YYYY-MM-DD_garmin_connect_export\')')
    parser.add_argument('-s', "--subdir",
                        help="the subdirectory for activity files (tcx, gpx etc.), supported placeholders are {YYYY} and {MM}"
                             " (default: export directory)")
    parser.add_argument('-u', '--unzip', action='store_true',
                        help='if downloading ZIP files (format: \'original\'), unzip the file and remove the ZIP file')
    parser.add_argument('-ot', '--originaltime', action='store_true',
                        help='will set downloaded (and possibly unzipped) file time to the activity start time')
    parser.add_argument('--desc', type=int, nargs='?', const=0, default=None,
                        help='append the activity\'s description to the file name of the download; limit size if number is given')
    parser.add_argument('-t', '--template', default=CSV_TEMPLATE,
                        help='template file with desired columns for CSV output')
    parser.add_argument('-fp', '--fileprefix', action='count',
                        help="set the local time as activity file name prefix")

    parsed_args = vars(parser.parse_args())
    return parsed_args


def csv_write_record(csv_filter, extract, actvty, details, activity_type_name, event_type_name):
    """
    Write out the given data as a CSV record
    """

    type_id = 4 if absent_or_null('activityType', actvty) else actvty['activityType']['typeId']
    parent_type_id = 4 if absent_or_null('activityType', actvty) else actvty['activityType']['parentTypeId']
    if present(parent_type_id, PARENT_TYPE_ID):
        parent_type_key = PARENT_TYPE_ID[parent_type_id]
    else:
        parent_type_key = None
        logging.warning("Unknown parentType %s, please tell script author", str(parent_type_id))

    # get some values from detail if present, from a otherwise
    start_latitude = from_activities_or_detail('startLatitude', actvty, details, 'summaryDTO')
    start_longitude = from_activities_or_detail('startLongitude', actvty, details, 'summaryDTO')
    end_latitude = from_activities_or_detail('endLatitude', actvty, details, 'summaryDTO')
    end_longitude = from_activities_or_detail('endLongitude', actvty, details, 'summaryDTO')

    csv_filter.set_column('id', str(actvty['activityId']))
    csv_filter.set_column('url', 'https://connect.garmin.com/modern/activity/' + str(actvty['activityId']))
    csv_filter.set_column('activityName', actvty['activityName'] if present('activityName', actvty) else None)
    csv_filter.set_column('description', actvty['description'] if present('description', actvty) else None)
    csv_filter.set_column('startTimeIso', extract['start_time_with_offset'].isoformat())
    csv_filter.set_column('startTime1123', extract['start_time_with_offset'].strftime(ALMOST_RFC_1123))
    csv_filter.set_column('startTimeMillis',
                          str(actvty['beginTimestamp']) if present('beginTimestamp', actvty) else None)
    csv_filter.set_column('startTimeRaw', details['summaryDTO']['startTimeLocal'] if present('startTimeLocal', details[
        'summaryDTO']) else None)
    csv_filter.set_column('endTimeIso',
                          extract['end_time_with_offset'].isoformat() if extract['end_time_with_offset'] else None)
    csv_filter.set_column('endTime1123', extract['end_time_with_offset'].strftime(ALMOST_RFC_1123) if extract[
        'end_time_with_offset'] else None)
    csv_filter.set_column('endTimeMillis',
                          str(actvty['beginTimestamp'] + extract['elapsed_seconds'] * 1000) if present('beginTimestamp',
                                                                                                       actvty) else None)
    csv_filter.set_column('durationRaw', str(round(actvty['duration'], 3)) if present('duration', actvty) else None)
    csv_filter.set_column('duration',
                          hhmmss_from_seconds(round(actvty['duration'])) if present('duration', actvty) else None)
    csv_filter.set_column('elapsedDurationRaw',
                          str(round(extract['elapsed_duration'], 3)) if extract['elapsed_duration'] else None)
    csv_filter.set_column('elapsedDuration', hhmmss_from_seconds(round(extract['elapsed_duration'])) if extract[
        'elapsed_duration'] else None)
    csv_filter.set_column('movingDurationRaw',
                          str(round(details['summaryDTO']['movingDuration'], 3)) if present('movingDuration', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('movingDuration',
                          hhmmss_from_seconds(round(details['summaryDTO']['movingDuration'])) if present(
                              'movingDuration', details['summaryDTO']) else None)
    csv_filter.set_column('distanceRaw',
                          "{0:.5f}".format(actvty['distance'] / 1000) if present('distance', actvty) else None)
    csv_filter.set_column('averageSpeedRaw',
                          kmh_from_mps(details['summaryDTO']['averageSpeed']) if present('averageSpeed', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('averageSpeedPaceRaw',
                          trunc6(pace_or_speed_raw(type_id, parent_type_id, actvty['averageSpeed'])) if present(
                              'averageSpeed', actvty) else None)
    csv_filter.set_column('averageSpeedPace',
                          pace_or_speed_formatted(type_id, parent_type_id, actvty['averageSpeed']) if present(
                              'averageSpeed', actvty) else None)
    csv_filter.set_column('averageMovingSpeedRaw',
                          kmh_from_mps(details['summaryDTO']['averageMovingSpeed']) if present('averageMovingSpeed',
                                                                                               details[
                                                                                                   'summaryDTO']) else None)
    csv_filter.set_column('averageMovingSpeedPaceRaw', trunc6(
        pace_or_speed_raw(type_id, parent_type_id, details['summaryDTO']['averageMovingSpeed'])) if present(
        'averageMovingSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('averageMovingSpeedPace', pace_or_speed_formatted(type_id, parent_type_id,
                                                                            details['summaryDTO'][
                                                                                'averageMovingSpeed']) if present(
        'averageMovingSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('maxSpeedRaw', kmh_from_mps(details['summaryDTO']['maxSpeed']) if present('maxSpeed', details[
        'summaryDTO']) else None)
    csv_filter.set_column('maxSpeedPaceRaw', trunc6(
        pace_or_speed_raw(type_id, parent_type_id, details['summaryDTO']['maxSpeed'])) if present('maxSpeed', details[
        'summaryDTO']) else None)
    csv_filter.set_column('maxSpeedPace', pace_or_speed_formatted(type_id, parent_type_id,
                                                                  details['summaryDTO']['maxSpeed']) if present(
        'maxSpeed', details['summaryDTO']) else None)
    csv_filter.set_column('elevationLoss',
                          str(round(details['summaryDTO']['elevationLoss'], 2)) if present('elevationLoss', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('elevationLossUncorr', str(round(details['summaryDTO']['elevationLoss'], 2)) if not actvty[
        'elevationCorrected'] and present('elevationLoss', details['summaryDTO']) else None)
    csv_filter.set_column('elevationLossCorr', str(round(details['summaryDTO']['elevationLoss'], 2)) if actvty[
                                                                                                            'elevationCorrected'] and present(
        'elevationLoss', details['summaryDTO']) else None)
    csv_filter.set_column('elevationGain',
                          str(round(details['summaryDTO']['elevationGain'], 2)) if present('elevationGain', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('elevationGainUncorr', str(round(details['summaryDTO']['elevationGain'], 2)) if not actvty[
        'elevationCorrected'] and present('elevationGain', details['summaryDTO']) else None)
    csv_filter.set_column('elevationGainCorr', str(round(details['summaryDTO']['elevationGain'], 2)) if actvty[
                                                                                                            'elevationCorrected'] and present(
        'elevationGain', details['summaryDTO']) else None)
    csv_filter.set_column('minElevation',
                          str(round(details['summaryDTO']['minElevation'], 2)) if present('minElevation', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('minElevationUncorr', str(round(details['summaryDTO']['minElevation'], 2)) if not actvty[
        'elevationCorrected'] and present('minElevation', details['summaryDTO']) else None)
    csv_filter.set_column('minElevationCorr', str(round(details['summaryDTO']['minElevation'], 2)) if actvty[
                                                                                                          'elevationCorrected'] and present(
        'minElevation', details['summaryDTO']) else None)
    csv_filter.set_column('maxElevation',
                          str(round(details['summaryDTO']['maxElevation'], 2)) if present('maxElevation', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('maxElevationUncorr', str(round(details['summaryDTO']['maxElevation'], 2)) if not actvty[
        'elevationCorrected'] and present('maxElevation', details['summaryDTO']) else None)
    csv_filter.set_column('maxElevationCorr', str(round(details['summaryDTO']['maxElevation'], 2)) if actvty[
                                                                                                          'elevationCorrected'] and present(
        'maxElevation', details['summaryDTO']) else None)
    csv_filter.set_column('elevationCorrected', 'true' if actvty['elevationCorrected'] else 'false')
    # csv_record += empty_record  # no minimum heart rate in JSON
    csv_filter.set_column('maxHRRaw',
                          str(details['summaryDTO']['maxHR']) if present('maxHR', details['summaryDTO']) else None)
    csv_filter.set_column('maxHR', "{0:.0f}".format(actvty['maxHR']) if present('maxHR', actvty) else None)
    csv_filter.set_column('averageHRRaw', str(details['summaryDTO']['averageHR']) if present('averageHR', details[
        'summaryDTO']) else None)
    csv_filter.set_column('averageHR', "{0:.0f}".format(actvty['averageHR']) if present('averageHR', actvty) else None)
    csv_filter.set_column('caloriesRaw', str(details['summaryDTO']['calories']) if present('calories', details[
        'summaryDTO']) else None)
    csv_filter.set_column('calories', "{0:.0f}".format(details['summaryDTO']['calories']) if present('calories',
                                                                                                     details[
                                                                                                         'summaryDTO']) else None)
    csv_filter.set_column('vo2max', str(actvty['vO2MaxValue']) if present('vO2MaxValue', actvty) else None)
    csv_filter.set_column('aerobicEffect',
                          str(round(details['summaryDTO']['trainingEffect'], 2)) if present('trainingEffect', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('anaerobicEffect', str(round(details['summaryDTO']['anaerobicTrainingEffect'], 2)) if present(
        'anaerobicTrainingEffect', details['summaryDTO']) else None)
    csv_filter.set_column('averageRunCadence',
                          str(round(details['summaryDTO']['averageRunCadence'], 2)) if present('averageRunCadence',
                                                                                               details[
                                                                                                   'summaryDTO']) else None)
    csv_filter.set_column('maxRunCadence', str(details['summaryDTO']['maxRunCadence']) if present('maxRunCadence',
                                                                                                  details[
                                                                                                      'summaryDTO']) else None)
    csv_filter.set_column('strideLength',
                          str(round(details['summaryDTO']['strideLength'], 2)) if present('strideLength', details[
                              'summaryDTO']) else None)
    csv_filter.set_column('steps', str(actvty['steps']) if present('steps', actvty) else None)
    csv_filter.set_column('averageCadence', str(actvty['averageBikingCadenceInRevPerMinute']) if present(
        'averageBikingCadenceInRevPerMinute', actvty) else None)
    csv_filter.set_column('maxCadence',
                          str(actvty['maxBikingCadenceInRevPerMinute']) if present('maxBikingCadenceInRevPerMinute',
                                                                                   actvty) else None)
    csv_filter.set_column('strokes', str(actvty['strokes']) if present('strokes', actvty) else None)
    csv_filter.set_column('averageTemperature',
                          str(details['summaryDTO']['averageTemperature']) if present('averageTemperature',
                                                                                      details['summaryDTO']) else None)
    csv_filter.set_column('minTemperature', str(details['summaryDTO']['minTemperature']) if present('minTemperature',
                                                                                                    details[
                                                                                                        'summaryDTO']) else None)
    csv_filter.set_column('maxTemperature', str(details['summaryDTO']['maxTemperature']) if present('maxTemperature',
                                                                                                    details[
                                                                                                        'summaryDTO']) else None)
    csv_filter.set_column('device', extract['device'] if extract['device'] else None)
    csv_filter.set_column('gear', extract['gear'] if extract['gear'] else None)
    csv_filter.set_column('activityTypeKey', actvty['activityType']['typeKey'].title() if present('typeKey', actvty[
        'activityType']) else None)
    csv_filter.set_column('activityType', value_if_found_else_key(activity_type_name,
                                                                  'activity_type_' + actvty['activityType'][
                                                                      'typeKey']) if present('activityType',
                                                                                             actvty) else None)
    csv_filter.set_column('activityParent', value_if_found_else_key(activity_type_name,
                                                                    'activity_type_' + parent_type_key) if parent_type_key else None)
    csv_filter.set_column('eventTypeKey',
                          actvty['eventType']['typeKey'].title() if present('typeKey', actvty['eventType']) else None)
    csv_filter.set_column('eventType',
                          value_if_found_else_key(event_type_name, actvty['eventType']['typeKey']) if present(
                              'eventType', actvty) else None)
    csv_filter.set_column('privacy', details['accessControlRuleDTO']['typeKey'] if present('typeKey', details[
        'accessControlRuleDTO']) else None)
    csv_filter.set_column('fileFormat', details['metadataDTO']['fileFormat']['formatKey'] if present('fileFormat',
                                                                                                     details[
                                                                                                         'metadataDTO']) and present(
        'formatKey', details['metadataDTO']['fileFormat']) else None)
    csv_filter.set_column('tz', details['timeZoneUnitDTO']['timeZone'] if present('timeZone',
                                                                                  details['timeZoneUnitDTO']) else None)
    csv_filter.set_column('tzOffset', extract['start_time_with_offset'].isoformat()[-6:])
    csv_filter.set_column('locationName', details['locationName'] if present('locationName', details) else None)
    csv_filter.set_column('startLatitudeRaw', str(start_latitude) if start_latitude else None)
    csv_filter.set_column('startLatitude', trunc6(start_latitude) if start_latitude else None)
    csv_filter.set_column('startLongitudeRaw', str(start_longitude) if start_longitude else None)
    csv_filter.set_column('startLongitude', trunc6(start_longitude) if start_longitude else None)
    csv_filter.set_column('endLatitudeRaw', str(end_latitude) if end_latitude else None)
    csv_filter.set_column('endLatitude', trunc6(end_latitude) if end_latitude else None)
    csv_filter.set_column('endLongitudeRaw', str(end_longitude) if end_longitude else None)
    csv_filter.set_column('endLongitude', trunc6(end_longitude) if end_longitude else None)
    csv_filter.set_column('sampleCount', str(extract['samples']['metricsCount']) if present('metricsCount', extract[
        'samples']) else None)

    csv_filter.write_row()


def logging_verbosity(verbosity):
    """Adapt logging verbosity, separately for logfile and console output"""
    logger = logging.getLogger()
    if not isinstance(verbosity, int):
        verbosity = 2
    for handler in logger.handlers:
        if isinstance(handler, logging.FileHandler):
            # this is the logfile handler
            level = logging.DEBUG if verbosity > 0 else logging.INFO
            handler.setLevel(level)
            logging.info('New logfile level: %s', logging.getLevelName(level))
        elif isinstance(handler, logging.StreamHandler):
            # this is the console handler
            level = logging.DEBUG if verbosity > 1 else (logging.INFO if verbosity > 0 else logging.WARN)
            handler.setLevel(level)
            logging.debug('New console log level: %s', logging.getLevelName(level))


def write_last_activity_index(settings_dir, activity_index, format):
    """
    Persists the index of the last exported activity for the given export format
    (see also method read_settings())
    :param settings_dir: Path to the pickle file
    :param activity_index: Positive integer
    :param format: Value of args["format"]
    """
    settings = read_settings(settings_dir)
    settings['activity_indices'][format] = activity_index

    file_name = join(settings_dir, ".settings")

    with open(file_name, "wb") as f:
        pickle.dump(settings, f)


def read_settings(settings_dir):
    """
    Reads the stored settings from the given download dir
    Expected pickle format is for instance {activity_indices={tcx=10, gpx=42, json=2, original=0}}
    :param settings_dir: Path to the settings file
    :return: dictionary with one key 'activity_indices', which is a dictionary of integer values for keys tcx, gpx,
    json and original. If settings are not found an initialized dictionary will be returned:
    dict(activity_indices=(tcx=0, gps=0, json=0, original=0))
    """
    file_name = join(settings_dir, ".settings")

    try:
        with open(file_name, "rb") as f:
            pick = pickle.load(f)
            return pick
    except IOError:
        return dict(activity_indices=dict(tcx=0, gpx=0, json=0, original=0))


class GarminConnect(object):
    """ Class to represent connection to GarminConnect"""

    urls = load_yaml(Path(__file__).parent.joinpath("settings.yaml"))["urls"]

    def __init__(self, username: str = None, password: str = None, export_dir: Path = None):
        self.session = requests.Session()  # main session object to hold all cookies, requests etc
        self.export_dir = export_dir or Path("exports")

        self.auth_ticket = self.login(self.session, username, password)

        self.activity_tyes = self.get_activity_types()
        self.event_types = self.get_event_types()
        self.userstats = self.get_userstats()

    def login(self, session: requests.Session, username: str, password: str) -> str:
        """
        Perform all HTTP requests to login to Garmin Connect.
        """
        username = username or input('Username: ')
        password = password or getpass()

        logger.info('Connecting to Garmin Connect...')
        logger.info('Connecting to %s', self.urls["LOGIN"])
        connect_response = session.get(self.urls["LOGIN"], params=LOGIN_PARAMS)

        # Fields that are passed in a typical Garmin login.
        post_data = {
            'username': username,
            'password': password,
            'embed': 'false',
            'rememberme': 'on'
        }

        headers = {
            'referer': self.urls["LOGIN"]
        }

        logger.info('Requesting Login ticket...')
        login_req = session.post(self.urls["LOGIN"], params=LOGIN_PARAMS, data=post_data, headers=headers)

        # Extract the ticket from the login response
        pattern = re.compile(r".*\?ticket=([-\w]+)\";.*", re.MULTILINE | re.DOTALL)
        match = pattern.match(login_req.text)
        if not match:
            raise RuntimeError('Couldn\'t find ticket in the login response. Cannot log in. '
                               'Did you enter the correct username and password?')
        login_ticket = match.group(1)
        print(' Done. Ticket=' + login_ticket)

        print("Authenticating...", end='')
        logging.info(f"Authentication URL {self.urls['POST_AUTH']},  ticket={login_ticket}")
        session.get(self.urls["POST_AUTH"], params={'ticket': login_ticket})

        return login_ticket

    def get_userstats(self) -> Dict:
        """ Get user stats and return dict from JSON response"""
        logging.info('Fetching user stats...')
        logging.info('Userstats page %s', self.urls["USERSTATS"])
        user_stats_req = self.session.get(self.urls["USERSTATS"])
        if user_stats_req.ok is True:
            return json.loads(user_stats_req.text)
        else:
            raise requests.HTTPError("Could not get user stats!")

    def get_activity_types(self) -> Dict:
        activity_type_req = self.session.get(self.urls["ACT_PROPS"])
        return load_properties(activity_type_req.text)

    def get_event_types(self) -> Dict:
        event_type_req = self.session.get(self.urls["EVT_PROPS"])
        return load_properties(event_type_req.text)

    def get_n_activites(self, count: Union[int, str]) -> int:
        """
        Gets activities

        :param count: Can be int number of activities, or 'all' for all activities, 'new' for new ones.
        :returns:
        """
        if isinstance(count, int):
            total_n = count
        elif count == 'all':
            total_n = int(self.userstats['userMetrics'][0]['totalActivities'])
        # elif count == 'new':
        # TODO implement cache

        #     total_n = int(self.userstats['userMetrics'][0]['totalActivities']) - \
        #               read_settings(args["directory"])['activity_indices'][args["format"]]
        else:
            raise ValueError(f"count must be int, 'all' or 'new'! Supplied count: {count}")
        if total_n == 0:
            logger.warning("No new activities.")
        return total_n

    def get_activity_details(self, activity_id: str) -> Dict:
        """ Gets detailed activity details """
        # Retrieve also the detail data from the activity (the one displayed on
        # the https://connect.garmin.com/modern/activity/xxx page), because some
        # data are missing from 'a' (or are even different)

        for tries in range(MAX_TRIES):
            activity_details_req = self.session.get(self.urls["ACTIVITY"] + f"/{activity_id}")
            details = json.loads(activity_details_req.text)
            if details.get('summaryDTO') is not None:
                break
            else:
                logging.warning(
                    f"Retrying activity details download for activityId {activity_id}")
        else:  # no break
            raise RuntimeError(
                f"Did not get summaryDTO after {MAX_TRIES} tries for activityId {activity_id}")

        return details

    def get_activities(self, count: Union[int, str]):
        downloaded_n = 0
        device_dict = dict()  # TODO Read from cache?
        total_n = self.get_n_activites(count)

        # This while loop will download data from the server in multiple chunks, if necessary.
        while downloaded_n < total_n:
            # Maximum chunk size 'LIMIT_MAXIMUM' ... 400 return status if over maximum.  So download
            # maximum or whatever remains if less than maximum.
            # As of 2018-03-06 I get return status 500 if over maximum
            if total_n - downloaded_n > LIMIT_MAXIMUM:
                num_to_download = LIMIT_MAXIMUM
            else:
                num_to_download = total_n - downloaded_n

            search_params = {'start': downloaded_n, 'limit': num_to_download}
            activity_list_req = self.session.get(self.urls["LIST"], params=search_params)

            # TODO Cache activities

            all_activities = json.loads(activity_list_req.text)
            if len(all_activities) != num_to_download:
                logging.warning('Expected %s activities, got %s.', num_to_download, len(all_activities))

            # Process each activity; start with the oldest one
            for i, activity in tqdm(enumerate(reversed(all_activities)), total=len(all_activities)):
                activity_id = str(activity['activityId'])
                logger.info(f"Processing Garmin Connect activity_id {activity_id}: {activity['activityName']}")
                activity_details = self.get_activity_details(activity_id=activity_id)

                extract = {}
                extract['start_time_with_offset'] = offset_date_time(activity['startTimeLocal'],
                                                                     activity['startTimeGMT'])
                elapsed_duration = activity_details['summaryDTO'][
                    'elapsedDuration'] if 'summaryDTO' in activity_details and 'elapsedDuration' in activity_details[
                    'summaryDTO'] else None
                extract['elapsed_duration'] = elapsed_duration if elapsed_duration else activity['duration']
                extract['elapsed_seconds'] = int(round(extract['elapsed_duration']))
                extract['end_time_with_offset'] = extract['start_time_with_offset'] + timedelta(
                    seconds=extract['elapsed_seconds'])

                print('\t' + extract['start_time_with_offset'].isoformat() + ', ', end='')
                print(hhmmss_from_seconds(extract['elapsed_seconds']) + ', ', end='')
                if 'distance' in activity and isinstance(activity['distance'], (float)):
                    print("{0:.3f}".format(activity['distance'] / 1000) + 'km')
                else:
                    print('0.000 km')

                extract['device'] = self.extract_device(device_dict, activity_details)

                # try to get the JSON with all the samples (not all activities have it...),
                # but only if it's really needed for the CSV output
                # extract['samples'] = None
                # if csv_filter.is_column_active('sampleCount'):
                #     try:
                #         # TODO implement retries here, I have observed temporary failures
                #         activity_measurements = session.get(
                #             ACTIVITY + activity_id + "/details").text
                #         write_to_file(args["directory"] + '/activity_' + activity_id + '_samples.json',
                #                       activity_measurements, 'w',
                #                       start_time_seconds)
                #         samples = json.loads(activity_measurements)
                #         extract['samples'] = samples
                #     except urllib.error.HTTPError:
                #         pass  # don't abort just for missing samples...
                #         # logging.info("Unable to get samples for %d", actvty['activityId'])
                #         # logging.exception(e)

                extract['gear'] = self.load_gear(activity_id)

                # Write stats to CSV.
                # csv_write_record(csv_filter, extract, activity, details, activity_type_name, event_type_name)

                self.download_activity(activity_details, activity['startTimeLocal'], format="ORIGINAL")

                # # Regardless if file was written or already exists
                # write_last_activity_index(args["directory"],
                #                           int(json_results['userMetrics'][0]['totalActivities']) -
                #                           total_n + current_index,
                #                           args["format"])

            # End for loop for activities of chunk
            downloaded_n += num_to_download

    def extract_device(self, device_dict: Dict, activity_details: Dict):
        """
        Try to get the device activity_details (and cache them, as they're used for multiple activities)
        """
        if "metadataDTO" not in activity_details:
            logging.warning("no metadataDTO")
            return None
        else:
            metadata = activity_details['metadataDTO']
            device_app_inst_id = metadata.get('deviceApplicationInstallationId')

        if device_app_inst_id is not None:
            if device_app_inst_id not in device_dict:
                # observed from my stock of activities:
                # activity_details['metadataDTO']['deviceMetaDataDTO']['deviceId'] == null -> device unknown
                # activity_details['metadataDTO']['deviceMetaDataDTO']['deviceId'] == '0' -> device unknown
                # activity_details['metadataDTO']['deviceMetaDataDTO']['deviceId'] == 'someid' -> device known
                device_dict[device_app_inst_id] = None
                device_meta = metadata.get('deviceMetaDataDTO')
                device_id = device_meta.get('deviceId')
                if 'deviceId' not in device_meta or device_id and device_id != '0':
                    device_json_req = self.session.get(self.urls["DEVICE"] + str(device_app_inst_id))
                    # export_dir.joinpath(f"device_{device_app_inst_id}.json").write_text(device_json_req.text)
                    if device_json_req.ok is False:
                        logging.warning(f"Device Details {device_app_inst_id} are empty")
                        device_dict[device_app_inst_id] = "device-id:" + str(device_app_inst_id)
                    else:
                        device_details = json.loads(device_json_req.text)
                        if 'productDisplayName' in device_details:
                            device_dict[device_app_inst_id] = device_details['productDisplayName'] + ' ' \
                                                              + device_details['versionString']
                        else:
                            logging.warning(f"Device activity_details {device_app_inst_id} incomplete")
            return device_dict[device_app_inst_id]
        else:
            return None

    def load_gear(self, activity_id: str):
        """ Retrieve the gear/equipment for an activity """

        gear_req = self.session.get(f"{self.urls['GEAR']}/{activity_id}")
        if gear_req.ok is True:
            params = {"activityId": activity_id}
            gear = json.loads(gear_req.text)
            if len(gear) > 0:
                gear_display_name = gear[0].get('displayName')
                gear_model = gear[0].get('customMakeModel')
                logging.debug("Gear for %s = %s/%s", activity_id, gear_display_name, gear_model)
                return gear_display_name if gear_display_name else gear_model
            else:
                return None
        else:
            logging.debug(f"Unable to get gear for activity_id {activity_id}")
            return None  # Don't abort just for missing gear

    def download_activity(self, activity_details: Dict, start_time_locale, format: str = "ORIGINAL"):
        """
        Write the data of the activity to a file, depending on the chosen data format
        """
        allowed_formats = ["ORIGINAL", "GPX", "JSON"]
        if format not in allowed_formats:
            raise ValueError(f"format '{format}' not recognised. Must be one of {allowed_formats}")
        activity_id = activity_details["activityId"]

        download_url = f"{self.urls[f'{format.upper()}_ACTIVITY']}/{activity_id}"
        download_params = {"full": "true"}
        start_time_locale = get_valid_filename(start_time_locale)  # Remove illegal characters
        if format != "ORIGINAL":
            download_filename = self.export_dir.joinpath(f"{start_time_locale}_{activity_id}.{format}")
        else:
            download_filename = self.export_dir.joinpath(f"{start_time_locale}_{activity_id}.zip")

        if download_filename.exists():
            logger.debug(f"Skipping already-existing file: {download_filename}")
            return False

        if format != 'JSON':
            dl_req = self.session.get(download_url, params=download_params)

            # Handle expected (though unfortunate) error codes; die on unexpected ones.
            if dl_req.status_code == 404 and format == "ORIGINAL":
                # For manual activities (i.e., entered in online without a file upload), there is
                # no original file. Write an empty file to prevent redownloading it.
                logging.info('Writing empty file since there was no original activity data...')
                raw_data = b''
            elif dl_req.ok is False:
                raise Exception('Failed. Got an HTTP error ' + str(dl_req.status_code) + ' for ' + download_url)
            else:
                raw_data = dl_req.content

        else:
            raw_data = activity_details

        Path(download_filename).absolute().write_bytes(raw_data)

        # Persist file
        if format == 'ORIGINAL':
            # Even manual upload of a GPX file is zipped, but we'll validate the extension.
            file_size = stat(download_filename).st_size
            logging.debug(f"Unzipping and removing original file, size is {file_size}")
            if file_size > 0:
                with open(download_filename, "rb") as zip_file:
                    zip_obj = zipfile.ZipFile(zip_file)
                    for name in zip_obj.namelist():
                        unzipped_name = Path(zip_obj.extract(name, self.export_dir))
                        file_type = unzipped_name.suffix
                        new_name = download_filename.with_suffix(file_type)
                        logging.debug(f"Renaming {unzipped_name} to {new_name}")
                        unzipped_name.rename(new_name)
            else:
                logger.warning(f"Skipping 0Kb zip file for activity_id {activity_id}")
                Path(download_filename).unlink()
        return True


def main(**kwargs):
    """
    Main entry point for gcexport.py
    """
    setup_logging()
    if len(kwargs) > 0:
        args = kwargs
        for key, value in kwargs.items():
            logging.debug(f"arg : {key} | value : {value}")
    else:
        args = parse_arguments()

    logging_verbosity(args.get("verbosity"))

    print('Welcome to Garmin Connect Exporter!')

    # Create directory for data files.
    export_dir = Path(args.get("export_dir"))
    export_dir.mkdir(parents=True, exist_ok=True)
    export_csv = export_dir.joinpath("activities.csv")

    garmin_connect = GarminConnect(username=args.get("username"), password=args.get("password"), export_dir=export_dir)

    activities = garmin_connect.get_activities(count="all")

    logger.debug(pprint(garmin_connect.userstats, width=200))

    logger.info(f"Export completed to {export_dir}")


if __name__ == "__main__":
    logger, log_filename = setup_logging(log_config_path="logging_config.yaml", log_dir="logs", module_name=__name__,
                                         default_level=logging.DEBUG)
    try:
        # main(sys.argv)
        test_args = {"count": "all",
                     "export_dir": r"C:\GitHub\garmin-connect-export\exports",
                     "format": "original",
                     "username": "cfculhane@gmail.com",
                     "password": "^wI&4Cf3J@wRAnYjF1Fp",
                     "subdir": "{YYYY}",
                     "template": CSV_TEMPLATE
                     }
        main(**test_args)
    except KeyboardInterrupt:
        print('Interrupted')
        sys.exit(0)
