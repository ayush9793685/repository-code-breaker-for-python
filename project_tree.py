# TEST STUB: the real project_tree module was not part of the upload.
def build_project_tree(project, descriptor, entries, analyze):
    return {"project": project, "descriptor": descriptor,
            "entries": [{"entry": e["entry_file"], "result": analyze(e)} for e in entries]}
def render_project_tree(h):
    return "\n".join(x["entry"] for x in h["entries"])
