"""Regression cases for the reported README/metadata project-role drift."""
import unittest

from check_package import check_roles

TRIO = ["Arthur Freitas Ramos", "David Barros Hulak",
        "Ruy Jose Guerra Barretto de Queiroz"]


def readme(authors, maintainers):
    return ("Project authors:\n\n" + "".join(f"- {name}\n" for name in authors)
            + "\nResponsible maintainers:\n\n"
            + "".join(f"- {name}\n" for name in maintainers))


class RoleConsistencyTests(unittest.TestCase):
    def test_current_trio_matches(self):
        check_roles({"authors": TRIO, "responsible_maintainers": TRIO}, readme(TRIO, TRIO))

    def test_reported_single_person_prose_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, "Stale combined"):
            check_roles({"authors": TRIO, "responsible_maintainers": TRIO},
                        "Authorship and maintenance remain with Arthur Freitas Ramos.")

    def test_metadata_only_author_drift_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, "Project authors.*differ"):
            check_roles({"authors": TRIO, "responsible_maintainers": TRIO[:1]},
                        readme(TRIO[:1], TRIO[:1]))

    def test_maintenance_drift_is_checked_separately(self):
        with self.assertRaisesRegex(AssertionError, "Responsible maintainers.*differ"):
            check_roles({"authors": TRIO, "responsible_maintainers": TRIO},
                        readme(TRIO, TRIO[:1]))

    def test_authorship_does_not_imply_maintenance(self):
        check_roles({"authors": TRIO, "responsible_maintainers": TRIO[:1]},
                    readme(TRIO, TRIO[:1]))

    def test_stale_prose_cannot_hide_beside_correct_lists(self):
        with self.assertRaisesRegex(AssertionError, "Stale combined"):
            check_roles({"authors": TRIO, "responsible_maintainers": TRIO},
                        readme(TRIO, TRIO)
                        + "\nAuthorship and maintenance remain with Arthur Freitas Ramos.")


if __name__ == "__main__":
    unittest.main()
