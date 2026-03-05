#include <iostream>
#include <string>
#include <vector>
#include <stdexcept>
#include <unordered_set>
#include <fstream>
#include <chrono>
#include <filesystem>

//noinspection UnusedIncludeDirective
#include <minizinc/builtins.hh> // potentially important for initializing libminizinc, even if the imported things are not used

#include <minizinc/parser.hh>
#include <minizinc/model.hh>
#include <minizinc/typecheck.hh>
#include <minizinc/ast.hh>
#include <minizinc/astiterator.hh>
#include <minizinc/prettyprinter.hh>
#include <minizinc/exception.hh>
#include <minizinc/file_utils.hh>
#include <minizinc/flatten_internal.hh>

#include "compiler.hpp"


using namespace MiniZinc;

int main(int argc, char** argv) {
  std::string redundant_ann = "redundant";
  std::string cons_ann_ignore = "nonredundant";
  std::string minizinc_stdlib_dir;
  bool prove_non_redundant = false;
  std::vector<std::string> positional_args;
  for (int i = 1; i < argc; ++i) {
    std::string arg(argv[i]);
    if (arg == "--prove-non-redundant") {
      prove_non_redundant = true;
    } else if (arg == "--redundant-ann") {
      if (i + 1 >= argc) {
        std::cerr << "missing value for --redundant-ann\n";
        return 64; // EX_USAGE
      }
      redundant_ann = argv[++i];
    } else if (arg.rfind("--redundant-ann=", 0) == 0) {
      redundant_ann = arg.substr(std::string("--redundant-ann=").size());
    } else if (arg == "--cons-ann-ignore") {
      if (i + 1 >= argc) {
        std::cerr << "missing value for --cons-ann-ignore\n";
        return 64; // EX_USAGE
      }
      cons_ann_ignore = argv[++i];
    } else if (arg.rfind("--cons-ann-ignore=", 0) == 0) {
      cons_ann_ignore = arg.substr(std::string("--cons-ann-ignore=").size());
    } else if (arg == "--minizinc-stdlib-dir") {
      if (i + 1 >= argc) {
        std::cerr << "missing value for --minizinc-stdlib-dir\n";
        return 64; // EX_USAGE
      }
      minizinc_stdlib_dir = argv[++i];
    } else if (arg.rfind("--minizinc-stdlib-dir=", 0) == 0) {
      minizinc_stdlib_dir = arg.substr(std::string("--minizinc-stdlib-dir=").size());
    } else {
      positional_args.push_back(arg);
    }
  }

  if (positional_args.empty()) {
    std::cerr << "usage: " << argv[0]
              << " [--prove-non-redundant] [--add-safety-assumptions] [--redundant-ann NAME] [--cons-ann-ignore NAME] [--minizinc-stdlib-dir DIR] path/to/model.mzn [path/to/data.dzn ...]\n";
    return 64; // EX_USAGE
  }

  try {
    // Create environment
    Env env;

    std::string filename = positional_args[0];
    std::ifstream file(filename);
    if (!file) {
      throw std::runtime_error("Cannot open file: " + filename);
    }

    std::string content((std::istreambuf_iterator<char>(file)),
                        std::istreambuf_iterator<char>());

    // Set up include paths for standard library
    std::vector<std::string> includePaths;
    if (!minizinc_stdlib_dir.empty()) {
      includePaths.push_back(minizinc_stdlib_dir);
    } else {
      for (const auto& path : std::vector<std::filesystem::path>{std::filesystem::current_path() / "mzn-to-lean/libminizinc/share/minizinc/std", std::filesystem::current_path() / "libminizinc/share/minizinc/std"}) {
        if (std::filesystem::exists(path)) {
          includePaths.push_back(path.string());
        }
      }
    }

    if (includePaths.empty()) {
      std::cerr << "Warning: MiniZinc include paths empty" << std::endl;
    }

    Model* model = parse_from_string(env, content, filename,
                                             includePaths,
                                             false, false, false, false, std::cerr);
    env.model(model);

    if (!model) {
      throw std::runtime_error("Failed to parse model");
    }

    std::vector<MiniZinc::TypeError> errors;
    typecheck(env, model, errors, /*ignoreUndefinedParameters=*/true,
                      /*allowMultiAssign=*/false, /*isFlatZinc=*/false);
    if (!errors.empty()) {
      for (auto& e : errors) e.print(std::cerr);  // or throw
      throw std::runtime_error("Type errors in model");
    }

    std::cerr << "Model parsed successfully. Size: " << model->size() << " items\n";

    //dumpFullModelAST(model, true); // print to stdout
    //exit(0);


    // Time both the Compiler instantiation and iter_items call together
    auto start_time = std::chrono::high_resolution_clock::now();
    Compiler visitor(redundant_ann, cons_ann_ignore, prove_non_redundant);
    iter_items(visitor, model);
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time);

    // Output timing information (stderr so stdout stays valid Lean)
    std::cerr << "Compiler + iter_items execution time: " << duration.count() << " μs" << std::endl;

    // Emit Lean code on stdout
    std::cout << visitor.get_full_lean_model();
    return 0;
  } catch (const LocationException& e) {
    std::cerr << "MiniZinc error at " << e.loc() << ": " << e.msg() << "\n";
    return 65;
  } catch (const Exception& e) {
    std::cerr << "MiniZinc error: " << e.msg() << "\n";
    return 65;
  } catch (const std::exception& e) {
    std::cerr << "Fatal: " << e.what() << "\n";
    return 70;
  }
}
