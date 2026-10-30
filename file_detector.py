# TEST STUB: the real file_detector (MongoDB-backed) was not part of the upload.
import os
_MAP = {".py": "python", ".c": "c", ".cpp": "cpp", ".java": "java", ".js": "js"}
def detect_file_type(path):
    return _MAP.get(os.path.splitext(path)[1].lower())
