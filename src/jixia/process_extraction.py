"""
Process extracted Lean4 data from .decl.json and .reference.json files.

1. first extract statements from jixia results
2. extract structures/class from ntp results
3. extract dependencies from reference files from jixia, map them to the associated statement, while ensuring the dependencies are from the full_statements_paths (usually Mathlib, and the project itself)

python -m jixia.process_extraction \
    --input_jixia_dir /local-scratch1/jla1045/analysis-lean4/.jixia \
    --input_ntp_dir /local-scratch1/jla1045/ntp-toolkit/Examples/Analysis/combined_decl.jsonl \
    --output_extraction_path /local-scratch1/jla1045/analysis-lean4/extracted_statement.jsonl \
    --output_dependency_path /local-scratch1/jla1045/analysis-lean4/dependencies.jsonl \
    --prefixes "Analysis." \
    --lean_project_path /local-scratch1/jla1045/analysis-lean4 \
    --repo "https://github.com/mikeljl/analysis-split" \
    --commit "497db5ed7dc9bbd3653a5e96e79723c1d9e968e9" \
    --full_statements_paths  /local-scratch1/jla1045/ntp-toolkit/Examples/Mathlib/combined_decl.jsonl /local-scratch1/jla1045/ntp-toolkit/Examples/Analysis/combined_decl.jsonl

"""

import json
import argparse
from pathlib import Path
from typing import List, Optional, Dict


def load_valid_names_from_jsonl_files(jsonl_paths: List[str]) -> Dict[str, str]:
    """
    Load all valid statement names from multiple JSONL files.
    Returns a dict mapping name -> module for valid dependencies.
    """
    valid_names: Dict[str, str] = {}
    
    for jsonl_path in jsonl_paths:
        path = Path(jsonl_path)
        if not path.exists():
            print(f'Warning: JSONL file does not exist: {jsonl_path}')
            continue
        
        with open(path, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                
                try:
                    obj = json.loads(line)
                    name = obj.get('name')
                    module = obj.get('module')
                    if name and module:
                        valid_names[name] = module
                except json.JSONDecodeError as e:
                    print(f'Warning: Failed to parse line {line_num} in {jsonl_path}: {e}')
                    continue
    
    return valid_names


def extract_module_name(filename: str, suffix: str) -> str:
    """
    Extract module name from filename.
    e.g., "Analysis.Misc.FiniteChoice.decl.json" -> "Analysis.Misc.FiniteChoice"
    """
    return filename.removesuffix(suffix)


def module_to_lean_path(module: str) -> str:
    """
    Convert module name to relative lean file path.
    e.g., "Analysis.MeasureTheory.Section_1_3_4" -> "Analysis/MeasureTheory/Section_1_3_4.lean"
    """
    return module.replace('.', '/') + '.lean'


def find_src_range_in_file(lean_file: Path, src: str) -> Optional[List[int]]:
    """
    Find the byte range of `src` in the lean file.
    Returns [start, end] byte positions, or None if not found.
    """
    if not lean_file.exists():
        return None
    
    with open(lean_file, 'rb') as f:
        content = f.read()
    
    # Encode src to bytes for byte-position search
    src_bytes = src.encode('utf-8')
    
    start = content.find(src_bytes)
    if start == -1:
        return None
    
    end = start + len(src_bytes)
    return [start, end]


def process_decl_file(filepath: Path, module_name: str, repo: Optional[str] = None, commit: Optional[str] = None) -> List[dict]:
    """
    Process a .decl.json file and extract relevant information.
    
    For each object:
    - Skip if computeKind is not "regular"
    - Extract name (joined with '.')
    - Extract full_code_range from ref.range
    - Extract source_signature_range from signature.range
    - Extract kind
    - Add module name
    """
    results = []
    
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    for obj in data:
        # Check computeKind - skip if not "regular"
        modifiers = obj.get('modifiers', {})
        compute_kind = modifiers.get('computeKind')
        visibility = modifiers.get('visibility')
        if compute_kind != 'regular' or visibility == "private":
            continue
        
        # Extract name (list of strings -> joined with '.')
        name_parts = obj.get('name', [])
        if not name_parts:
            print(f'Warning: {filepath} has no name')
            continue
        try:
            name = '.'.join(name_parts)
        except Exception as e:
            print(f"error processing name: {name_parts} in {filepath}")
            continue

        
        # Extract full_code_range from ref.range
        ref = obj.get('ref', {})
        full_code_range = ref.get('range')
        if full_code_range is None:
            print(f'Warning: {filepath} : {name} has no full_code_range')
            continue
        
        # Extract source_signature_range from signature.range
        signature = obj.get('signature', {})
        source_signature_range = signature.get('range')
        if source_signature_range is None:
            print(f'Warning: {filepath} : {name}: {obj.get("kind")} has no source_signature_range')
        
        # Extract kind
        kind = obj.get('kind')
        if kind is None:
            print(f'Warning: {filepath} : {name} has no kind')
        
        # Build result object
        result = {
            'name': name,
            'full_code_range': full_code_range,
            'source_signature_range': source_signature_range,
            'kind': kind,
            'module': module_name,
            'repo': repo,
            'commit': commit
        }
        results.append(result)
    
    return results


def process_input_ntp_dir(
    input_ntp_dir_path: Path,
    lean_project_path: Path,
    prefixes: List[str],
    repo: Optional[str] = None,
    commit: Optional[str] = None
) -> List[dict]:
    """
    Process ntp combined_decl.jsonl file for structure, class kinds.
    
    For each matching entry:
    - Filter by kind: only keep "structure", "class"
    - Filter by module prefix if prefixes are provided
    - Find the src in the corresponding .lean file to get the byte range
    - Return formatted result with name, full_code_range, source_signature_range (null), kind, module
    """
    results = []
    target_kinds = {'structure', 'class'}
    
    with open(input_ntp_dir_path, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            
            try:
                obj = json.loads(line)
            except json.JSONDecodeError as e:
                print(f'Warning: Failed to parse line {line_num} in {input_ntp_dir_path}: {e}')
                continue
            
            # Filter by kind
            kind = obj.get('kind')
            if kind not in target_kinds:
                continue
            
            # Get module
            module = obj.get('module')
            if module is None:
                print(f'Warning NTP: Line {line_num} has no module')
                continue
            
            # Filter by prefix if specified
            if prefixes:
                matches_prefix = any(module.startswith(prefix) for prefix in prefixes)
                if not matches_prefix:
                    continue
            
            # Get name
            name = obj.get('name')
            if name is None:
                print(f'Warning NTP: Line {line_num} has no name')
                continue
            
            # Get src
            src = obj.get('src')
            if src is None:
                print(f'Warning: {module} : {name} has no src')
                continue
            
            # Find the lean file
            lean_relative_path = module_to_lean_path(module)
            lean_file = lean_project_path / lean_relative_path
            
            # Find src range in file
            full_code_range = find_src_range_in_file(lean_file, src)
            if full_code_range is None:
                print(f'Warning: Could not find src for {name} in {lean_file}')
                continue
            
            # Build result object
            result = {
                'name': name,
                'full_code_range': full_code_range,
                'source_signature_range': None,
                'kind': kind,
                'module': module,
                'repo': repo,
                'commit': commit
            }
            results.append(result)
    
    return results


def process_reference_files(
    input_jixia_dir: Path,
    prefixes: List[str],
    statements_by_module: Dict[str, List[dict]],
    valid_names: Dict[str, str],
    repo: Optional[str] = None,
    commit: Optional[str] = None
) -> List[dict]:
    """
    Process .reference.json files to extract dependencies for each statement.
    
    For each reference:
    - Check if the reference range is fully within a statement's full_code_range
    - Skip self-references (reference_name == statement name)
    - Only include dependencies that exist in valid_names
    
    Returns a list of dependency objects with name, module, dependencies, repo, commit.
    """
    ref_suffix = '.reference.json'
    ref_files = find_matching_files(input_jixia_dir, prefixes, ref_suffix)
    
    print(f"\nFound {len(ref_files)} .reference.json files to process")
    
    # Build dependency map: (module, statement_name) -> {full_code_range, deps: {(dep_name, dep_module): [ranges]}}
    dependency_map: Dict[tuple, dict] = {}
    
    for filepath in ref_files:
        module_name = extract_module_name(filepath.name, ref_suffix)
        
        # Get statements for this module
        module_statements = statements_by_module.get(module_name, [])
        if not module_statements:
            print(f'Warning REF: {module_name} has no extracted statements')
            continue
        
        # Load reference data
        with open(filepath, 'r', encoding='utf-8') as f:
            try:
                references = json.load(f)
            except json.JSONDecodeError as e:
                print(f'Warning: Failed to parse {filepath}: {e}')
                continue
        
        # Process each reference
        for ref in references:
            ref_name = ref.get('reference_name')
            ref_range = ref.get('range')
            
            if ref_name is None or ref_range is None or len(ref_range) != 2:
                print(f"Warning REF: Ill-formed reference {ref} from {filepath}")
                continue
            
            ref_start, ref_end = ref_range
            
            # Check if this reference_name is in the valid names database
            if ref_name not in valid_names:
                continue
            
            # Find which statement this reference belongs to
            for stmt in module_statements:
                stmt_name = stmt['name']
                full_code_range = stmt['full_code_range']

                # if stmt_name.endswith('._example'):
                #     continue
                
                if full_code_range is None or len(full_code_range) != 2:
                    continue
                
                stmt_start, stmt_end = full_code_range
                
                # Check if reference range is fully within statement's full_code_range
                if ref_start >= stmt_start and ref_end <= stmt_end:
                    # Skip self-references
                    if ref_name == stmt_name:
                        continue
                    
                    # Add to dependency map with range info
                    # Use full_code_range in key to handle duplicate names (e.g., multiple ._example)
                    key = (module_name, stmt_name, tuple(full_code_range))
                    if key not in dependency_map:
                        dependency_map[key] = {
                            'full_code_range': full_code_range,
                            'deps': {}
                        }
                    
                    dep_module = valid_names[ref_name]
                    dep_key = (ref_name, dep_module)
                    if dep_key not in dependency_map[key]['deps']:
                        dependency_map[key]['deps'][dep_key] = []
                    dependency_map[key]['deps'][dep_key].append(ref_range)
    
    # Build result list
    results = []
    for (module_name, stmt_name, _range_tuple), stmt_data in dependency_map.items():
        full_code_range = stmt_data['full_code_range']
        deps_dict = stmt_data['deps']
        
        # Sort by name for consistent output
        sorted_dep_keys = sorted(deps_dict.keys(), key=lambda x: x[0])
        dependencies = []
        for dep_name, dep_module in sorted_dep_keys:
            ranges = deps_dict[(dep_name, dep_module)]
            # Sort ranges by start position and remove duplicates
            unique_ranges = sorted(set(tuple(r) for r in ranges), key=lambda x: x[0])
            dependencies.append({
                'name': dep_name,
                'module': dep_module,
                'ranges': [list(r) for r in unique_ranges]
            })
        
        result = {
            'name': stmt_name,
            'module': module_name,
            'full_code_range': full_code_range,
            'dependencies': dependencies,
            'repo': repo,
            'commit': commit
        }
        results.append(result)
    
    return results


def find_matching_files(directory: Path, prefixes: List[str], suffix: str) -> List[Path]:
    """
    Find all files in directory that:
    - Start with one of the given prefixes
    - End with the given suffix
    """
    matching_files = []
    
    for filepath in directory.iterdir():
        if not filepath.is_file():
            continue
        
        filename = filepath.name
        
        # Check if file ends with the suffix
        if not filename.endswith(suffix):
            continue
        
        # Check if file starts with one of the prefixes
        if prefixes:
            matches_prefix = any(filename.startswith(prefix) for prefix in prefixes)
            if not matches_prefix:
                continue
        
        matching_files.append(filepath)
    
    return sorted(matching_files)


def process_extraction(
    input_jixia_dir: str,
    output_extraction_path: str,
    prefixes: Optional[List[str]] = None,
    input_ntp_dir: Optional[str] = None,
    lean_project_path: Optional[str] = None,
    repo: Optional[str] = None,
    commit: Optional[str] = None,
    full_statements_paths: Optional[List[str]] = None,
    output_dependency_path: Optional[str] = None
) -> None:
    """
    Process extracted Lean4 data from a directory.
    
    Args:
        input_jixia_dir: Directory containing extracted .decl.json and .reference.json files
        output_extraction_path: Path to output JSONL file
        prefixes: List of prefixes to filter files (only process files starting with these)
        input_ntp_dir: Path to ntp combined_decl.jsonl file for structure/class
        lean_project_path: Path to Lean project root (required if input_ntp_dir is provided)
        repo: GitHub repository URL
        commit: Git commit hash
        full_statements_paths: List of paths to JSONL files containing valid statement names
        output_dependency_path: Path to output dependency JSONL file
    """
    input_path = Path(input_jixia_dir)
    
    if not input_path.exists():
        raise ValueError(f"Input directory does not exist: {input_jixia_dir}")
    
    if not input_path.is_dir():
        raise ValueError(f"Input path is not a directory: {input_jixia_dir}")
    
    prefixes = prefixes or []
    
    # Process .decl.json files
    decl_suffix = '.decl.json'
    decl_files = find_matching_files(input_path, prefixes, decl_suffix)
    
    print(f"Found {len(decl_files)} .decl.json files to process")
    
    all_results = []
    
    for filepath in decl_files:
        module_name = extract_module_name(filepath.name, decl_suffix)
        results = process_decl_file(filepath, module_name, repo=repo, commit=commit)
        all_results.extend(results)
        #print(f"  Processed {filepath.name}: {len(results)} declarations")
    
    print(f"Processed {len(all_results)} declarations from .decl.json files")
    
    # Process input_ntp_dir if provided
    if input_ntp_dir:
        if lean_project_path is None:
            raise ValueError("--lean_project_path is required when --input_ntp_dir is provided")
        
        ntp_path = Path(input_ntp_dir)
        lean_path = Path(lean_project_path)
        
        if not ntp_path.exists():
            raise ValueError(f"input_ntp_dir file does not exist: {input_ntp_dir}")
        
        if not lean_path.exists():
            raise ValueError(f"lean_project_path does not exist: {lean_project_path}")
        
        print(f"\nProcessing input_ntp_dir: {input_ntp_dir}")
        ntp_results = process_input_ntp_dir(ntp_path, lean_path, prefixes, repo=repo, commit=commit)
        all_results.extend(ntp_results)
        print(f"Added {len(ntp_results)} structure/class declarations from input_ntp_dir")
    
    # Write results to JSONL
    output_file = Path(output_extraction_path)
    output_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_file, 'w', encoding='utf-8') as f:
        for result in all_results:
            f.write(json.dumps(result, ensure_ascii=False) + '\n')
    
    print(f"\nWrote {len(all_results)} total entries to {output_extraction_path}")
    
    # Process dependencies if output_dependency_path is provided
    if output_dependency_path and full_statements_paths:
        # Load valid names from all provided JSONL files
        print(f"\nLoading valid statement names from {len(full_statements_paths)} JSONL file(s)...")
        valid_names = load_valid_names_from_jsonl_files(full_statements_paths)
        print(f"Loaded {len(valid_names)} valid statement names")
        
        # Build statements_by_module from all_results
        statements_by_module: Dict[str, List[dict]] = {}
        for stmt in all_results:
            module = stmt.get('module')
            if module:
                if module not in statements_by_module:
                    statements_by_module[module] = []
                statements_by_module[module].append(stmt)
        
        # Process reference files
        dependency_results = process_reference_files(
            input_jixia_dir=input_path,
            prefixes=prefixes,
            statements_by_module=statements_by_module,
            valid_names=valid_names,
            repo=repo,
            commit=commit
        )
        
        # Write dependency results to JSONL
        dep_output_file = Path(output_dependency_path)
        dep_output_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(dep_output_file, 'w', encoding='utf-8') as f:
            for result in dependency_results:
                f.write(json.dumps(result, ensure_ascii=False) + '\n')
        
        print(f"\nWrote {len(dependency_results)} dependency entries to {output_dependency_path}")


def main():
    parser = argparse.ArgumentParser(
        description='Process extracted Lean4 data from .decl.json files'
    )
    parser.add_argument(
        '--input_jixia_dir',
        type=str,
        required=True,
        help='Directory containing extracted .decl.json and .reference.json files'
    )
    parser.add_argument(
        '--output_extraction_path',
        type=str,
        required=True,
        help='Path to output JSONL file'
    )
    parser.add_argument(
        '--prefixes',
        type=str,
        nargs='*',
        default=[],
        help='Prefixes to filter files (only process files starting with these prefixes)'
    )
    parser.add_argument(
        '--input_ntp_dir',
        type=str,
        default=None,
        help='Path to ntp combined_decl.jsonl file for structure/class declarations'
    )
    parser.add_argument(
        '--lean_project_path',
        type=str,
        default=None,
        help='Path to Lean project root (required if --input_ntp_dir is provided)'
    )
    parser.add_argument(
        '--repo',
        type=str,
        default=None,
        help='GitHub repository URL'
    )
    parser.add_argument(
        '--commit',
        type=str,
        default=None,
        help='Git commit hash'
    )
    parser.add_argument(
        '--full_statements_paths',
        type=str,
        nargs='*',
        default=None,
        help='Paths to JSONL files containing valid statement names for dependency checking'
    )
    parser.add_argument(
        '--output_dependency_path',
        type=str,
        default=None,
        help='Path to output dependency JSONL file'
    )
    
    args = parser.parse_args()
    
    process_extraction(
        input_jixia_dir=args.input_jixia_dir,
        output_extraction_path=args.output_extraction_path,
        prefixes=args.prefixes,
        input_ntp_dir=args.input_ntp_dir,
        lean_project_path=args.lean_project_path,
        repo=args.repo,
        commit=args.commit,
        full_statements_paths=args.full_statements_paths,
        output_dependency_path=args.output_dependency_path
    )


if __name__ == '__main__':
    main()
